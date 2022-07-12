//map.h

template<typename KeyType, typename ValueType>

class Map{
    public: 
    
    //constructor 
    //usage:  Map<KeyType, ValueType> map;
        Map();
    
    //destructor
    //virtual ~Map();
        ~Map();
    
    //returns the number of entries in the map
    //usage: int nEntries = map.size();
        int size() const;

    //returns if the map contains is empty
    //usage: if (map.empty()) ...
        bool empty() const;

    //assigns key with a value, any previous value associated with the key are replaced 
    //usage: map.put(key, value);
        void put(const KeyType& key, const ValueType& value);

    //Returns the value associated with the key in the map. Returns default value for ValueType 
    //usage: ValueType value = map.get(key);
        ValueType get(const KeyType& key) const;

    //Returns if there is the key in the map
    //Usage: if (map.containsKey(key)) ...
        bool containsKey(const KeyType& key) const;

    //Deletes the element associated with the key
    //Usage: map.eraseEl(key);
        void eraseEl(const KeyType& key);

    //Deletes all elemenst of the map
    //Usage: map.clear();
        void clear();
        //Iterator begin();
        //Iterator end();


    //Selects the value associated with a key. If the key is present, the function will return 
    //a reference to the value associated with it. If the key doesn't exist, then new entry will be created in the map. 
    ValueType& operator[] (const KeyType& key);
    ValueType operator[](const KeyType& key) const;


    //Convert the map to a string of the same entries
    std::string toString();
};


