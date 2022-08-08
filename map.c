#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <string.h>
#include <limits.h>
#include <stddef.h>
#include "map.h"
#include "map-impl.c"

#include <papi.h>

#ifdef CAPACITY_POW2
#include "map-impl-pow2.h"
#else
#include "map-impl.h"
#endif

struct Map {
  int* busybits;
  void** keyps;
  unsigned* khs;
  int* chns;
  int* vals;
  unsigned capacity;
  unsigned size;
  map_keys_equality* keys_eq;
  map_key_hash* khash;
};

struct int_key
    {
      uint16_t int_src_port;
      uint16_t dst_port;
      uint32_t int_src_ip;
      uint32_t dst_ip;
      uint16_t int_device_id;
      uint8_t protocol;
    };


 
unsigned int map_allocate(map_keys_equality* keq,  map_key_hash* khash,
                            unsigned capacity,
                            struct Map** map_out)

{

  #ifdef CAPACITY_POW2
  if (capacity == 0 || (capacity & (capacity - 1)) != 0) {
      return 0;
  }
  #else
  #endif

  struct Map* old_map_val = *map_out;
  struct Map* map_alloc = (struct Map*) malloc(sizeof(struct Map));

  if (map_alloc == NULL) return 0;

  *map_out = (struct Map*) map_alloc;
  int* bbs_alloc = (int*) malloc(sizeof(int)*(int)capacity);
  if (bbs_alloc == NULL) {
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->busybits = bbs_alloc;
  void** keyps_alloc = (void**) malloc(sizeof(void*)*(int)capacity);
  if (keyps_alloc == NULL) {
    free(bbs_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->keyps = keyps_alloc;
  unsigned* khs_alloc = (unsigned*) malloc(sizeof(unsigned)*(int)capacity);
  if (khs_alloc == NULL) {
    free(keyps_alloc);
    free(bbs_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->khs = khs_alloc;
  int* chns_alloc = (int*) malloc(sizeof(int)*(int)capacity);
  if (chns_alloc == NULL) {
    free(khs_alloc);
    free(keyps_alloc);
    free(bbs_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->chns = chns_alloc;
  int* vals_alloc = (int*) malloc(sizeof(int)*(int)capacity);
  if (vals_alloc == NULL) {
    free(chns_alloc);
    free(khs_alloc);
    free(keyps_alloc);
    free(bbs_alloc);
    free(map_alloc);
    *map_out = old_map_val;
    return 0;
  }
  (*map_out)->vals = vals_alloc;
  (*map_out)->capacity = capacity;
  (*map_out)->size = 0;
  (*map_out)->keys_eq = keq;
  (*map_out)->khash = khash;

  map_impl_init((*map_out)->busybits,
                keq,
                (*map_out)->keyps,
                (*map_out)->khs,
                (*map_out)->chns,
                (*map_out)->vals,
                capacity);
  return 1;
}

int map_get(struct Map* map, void* key, int* value_out)

{
  map_key_hash* khash = map->khash;
  unsigned hash = khash(key);
  return map_impl_get(map->busybits,
                      map->keyps,
                      map->khs,
                      map->chns,
                      map->vals,
                      key,
                      map->keys_eq,
                      hash,
                      value_out,
                      map->capacity);
}

void map_put(struct Map* map, void* key, int value)

{
  map_key_hash* khash = map->khash;
  unsigned hash = khash(key);
  map_impl_put(map->busybits,
               map->keyps,
               map->khs,
               map->chns,
               map->vals,
               key, hash, value,
               map->capacity);
  ++map->size;
 
}



void map_erase(struct Map* map, void* key, void** trash)

{
  map_key_hash* khash = map->khash;
  unsigned hash = khash(key);
  map_impl_erase(map->busybits,
                 map->keyps,
                 map->khs,
                 map->chns,
                 key,
                 map->keys_eq,
                 hash,
                 map->capacity,
                 trash);
  --map->size;

}

unsigned map_size(struct Map* map){

  return map->size;
 
}

static long long wrap(long long x)
//@ requires true;
//@ ensures result == _wrap(x) &*& INT_MIN <= result &*& result <= INT_MAX;
{
  //@ div_rem(x, INT_MAX);
  return x % INT_MAX;
}

bool int_key_eq(void *a, void *b)
//@ requires [?f1]int_k_p(a, ?ak) &*& [?f2]int_k_p(b, ?bk);
//@ ensures [f1]int_k_p(a, ak) &*& [f2]int_k_p(b, bk) &*& (false == result ? (ak != bk) : (ak == bk));
{
  struct int_key *k1 = a;
  struct int_key *k2 = b;
  return k1->int_src_port == k2->int_src_port && k1->dst_port == k2->dst_port && k1->int_src_ip == k2->int_src_ip && k1->dst_ip == k2->dst_ip && k1->int_device_id == k2->int_device_id && k1->protocol == k2->protocol;
}

int int_key_hash(void *key)
//@ requires [?f]int_k_p(key, ?k);
//@ ensures [f]int_k_p(key, k) &*& result == int_hash(k);
{
  struct int_key *ik = key;

  long long hash = ik->int_src_port;
  hash *= 31;

  hash += ik->dst_port;
  hash *= 31;

  hash += ik->int_src_ip;
  hash *= 31;

  hash += ik->dst_ip;
  hash *= 31;

  hash += ik->int_device_id;
  hash *= 31;

  hash += ik->protocol;

  hash = wrap(hash);

  return (int)hash;
}


int main (int argc, char** argv){

    struct Map *map_out;
    unsigned capacity;
    capacity = 100;
    struct int_key *k1 = malloc(sizeof(*k1)*capacity);
    struct int_key *k2 = malloc(sizeof *k2);
    map_allocate(&int_key_eq, &int_key_hash, capacity, &map_out);

//PAPI starts here

int retval;
int EventSet = PAPI_NULL;
long long values1[6], values2[6];
//, values3[6], values4[6], values5[6], values6[6];
const char *event_names[] = {"PAPI_TOT_CYC", "PAPI_TOT_INS", "PAPI_L1_DCM", "PAPI_L1_ICM", "PAPI_L2_TCM", "PAPI_L3_TCM"};
//PAPI initialization
 retval = PAPI_library_init(PAPI_VER_CURRENT);

if (retval != PAPI_VER_CURRENT){
    fprintf(stderr, "Error initializing PAPI! %s\n",
            PAPI_strerror(retval));
        return 0;
}

//create an eventset


retval = PAPI_create_eventset(&EventSet);
if (retval != PAPI_OK){
    fprintf(stderr, "Error creating eventset 1! %s\n",
            PAPI_strerror(retval));
}

//adding named events
retval = PAPI_add_named_event(EventSet, event_names[0]);
if (retval != PAPI_OK){
    fprintf(stderr, "Error adding PAPI_tot_ins: %s\n",
            PAPI_strerror(retval));
}

retval = PAPI_add_named_event(EventSet, event_names[1]);
if (retval != PAPI_OK){
    fprintf(stderr, "Error adding event[%s]: %s\n", event_names[1],
            PAPI_strerror(retval));
}

retval = PAPI_add_named_event(EventSet, event_names[2]);
if (retval != PAPI_OK){
    fprintf(stderr, "Error adding event[%s]: %s\n", event_names[2],
            PAPI_strerror(retval));
}

retval = PAPI_add_named_event(EventSet, event_names[3]);
if (retval != PAPI_OK){
    fprintf(stderr, "Error adding event[%s]: %s\n", event_names[3],
            PAPI_strerror(retval));
}

retval = PAPI_add_named_event(EventSet, event_names[4]);
if (retval != PAPI_OK){
    fprintf(stderr, "Error adding event[%s]: %s\n", event_names[4],
            PAPI_strerror(retval));
}
 
/* retval = PAPI_add_named_event(EventSet, event_names[5]);
if (retval != PAPI_OK){
    fprintf(stderr, "Error adding event[%s]: %s\n", event_names[5],
            PAPI_strerror(retval));
} */



PAPI_reset(EventSet);
retval = PAPI_start(EventSet);

if (retval!=PAPI_OK){
    fprintf(stderr, "Error starting CUDA: %s\n",
            PAPI_strerror(retval));
}
 

/* int SIZE = 100;
int keys[SIZE];
int value;

for (int i = 0; i < SIZE; i++){
  printf("The Key №: %d  : ", (i+1));
    keys[i] = rand()%100;
    printf("%d\n", keys[i]);

    printf("The Value  : ");
    value = rand()%1000;
    printf("%d\n", value);

        void *key_ptr = &keys;
        int *value_ptr = &value;

        map_put(map_out, &key_ptr, value);
        printf("value added %d\n", map_get(map_out, &key_ptr, value_ptr));
        printf("\n");
    }
    */



/*   char key1[] = "qwe123";
  void *key_ptr1 = &key1;
  int value1 = 27;
  int *value_ptr1 = &value1;

  char key2[] = "qwe124";
  void *key_ptr2 = &key2;
  int value2 = 24;
  int *value_ptr2 = &value2;

  char key3[] = "qwe125";
  void *key_ptr3 = &key3;
  int value3 = 24;
  int *value_ptr3 = &value3; */
 
/*
  map_put(map_out, &key_ptr1, value1);
  map_put(map_out, &key_ptr2, value2);
  map_put(map_out, &key_ptr3, value3);

  printf("%d\n", map_get(map_out, &key_ptr1, value_ptr1));
  printf("%19s, %d\n", key_ptr1, value1);

  printf("%d\n", map_get(map_out, &key_ptr2, value_ptr2));
  printf("%19s, %d\n", key_ptr2, value2);

  printf("%d\n", map_get(map_out, &key_ptr3, value_ptr3));
  printf("%19s, %d\n", key_ptr3, value3);
 */

retval = PAPI_stop(EventSet, values1);
if((retval != PAPI_OK) ){
    fprintf(stderr, "Error stopping: %s\n",
                PAPI_strerror(retval));
} else {
  for (int i = 0; i < 5; i++){
    printf("measured %lld %s  \t\n",  values1[i], event_names[i]);
  }
  printf("\n");
}
    

  
PAPI_reset(EventSet);
retval = PAPI_start(EventSet);

if (retval!=PAPI_OK){
    fprintf(stderr, "Error starting CUDA: %s\n",
            PAPI_strerror(retval));
}
 

int SIZE = 100;
int keys[SIZE];
int value;

for (int i = 0; i < SIZE; i++){
  //printf("The Key №: %d  : ", (i+1));
    keys[i] = rand()%100;
    //printf("%d\n", keys[i]);

    //printf("The Value  : ");
    value = rand()%1000;
    //printf("%d\n", value);

        void *key_ptr = &keys;
        int *value_ptr = &value;

        map_put(map_out, &key_ptr, value);
        /* printf("value added %d\n", map_get(map_out, &key_ptr, value_ptr));
        printf("\n");   */
    }

retval = PAPI_stop(EventSet, values1);
if((retval != PAPI_OK) ){
    fprintf(stderr, "Error stopping: %s\n",
                PAPI_strerror(retval));
} else {
  for (int i = 0; i < 5; i++){
    printf("measured %lld %s  \t\n",  values2[i], event_names[i]);
  }
}
    return 0;

PAPI_cleanup_eventset(EventSet);
PAPI_destroy_eventset(&EventSet);

}



