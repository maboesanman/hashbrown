
use crate::hash_map::{DefaultHashBuilder, make_hash};
use crate::map::{make_insert_hash, Drain, HashMap, IntoIter, Iter, IterMut};
use crate::raw::{Allocator, Bucket, Global, RawTable};
use core::borrow::Borrow;
use core::fmt::{self, Debug};
use core::hash::{BuildHasher, Hash};

impl<K, V, S, A> HashMap<K, V, S, A>
where
    K: Eq + Hash,
    S: BuildHasher,
    A: Allocator + Clone,
{
    /// get an EntryRef, cloning the key if vacant.
    pub fn rustc_entry_ref(&mut self, key: &K) -> RustcEntryRef<'_, K, V, S, A>
    where
        K: Hash + Eq + Clone,
    {
        let hash = make_hash::<K, K, S>(&self.hash_builder, key);
        match self.table.find(hash, |(ref k, _)| key.eq(k)) {
            Some(elem) => RustcEntryRef::Occupied(RustcOccupiedEntryRef { hash, elem, map: self }),
            None => RustcEntryRef::Vacant(RustcVacantEntryRef { hash, key: key.clone(), map: self })
        }
    }

    /// get an occupied entry if it exists.
    pub fn rustc_occupied_entry_ref<Q>(&mut self, key: &Q) -> Option<RustcOccupiedEntryRef<'_, K, V, S, A>>
    where
        K: Borrow<Q>,
        Q: Hash + Eq
    {
        let hash = make_hash::<K, Q, S>(&self.hash_builder, key);
        self.table.find(hash, move |x| key.eq(x.0.borrow())).map(|elem| {
            RustcOccupiedEntryRef { hash, elem, map: self }
        })
    }
    
    /// get a vacant entry. return the key if it's occupied.
    pub fn rustc_vacant_entry_ref(&mut self, key: K) -> Result<RustcVacantEntryRef<'_, K, V, S, A>, K> {
        let hash = make_insert_hash::<K, S>(&self.hash_builder, &key);
        match self.table.find(hash, |(ref k, _)| key.eq(k)) {
            Some(_) => Err(key),
            None => Ok(RustcVacantEntryRef { hash, key, map: self }),
        }
    }
    
    /// get a raw entry from a hash and a matcher function.
    pub fn rustc_raw_entry_from_hash<F>(&mut self, hash: u64, mut eq: F) -> RustcRawEntryRef<'_, K, V, S, A>
    where
        for<'b> F: FnMut(&'b K) -> bool
    {
        match self.table.find(hash, |(ref k, _)| eq(k)) {
            Some(elem) => RustcRawEntryRef::Occupied(RustcOccupiedEntryRef { hash, elem, map: self }),
            None => RustcRawEntryRef::Vacant(RustcRawVacantEntryRef { hash, map: self })
        }
    }
    
    /// get a raw entry from a hash. you can only insert into this if your key hashes to the query hash.
    pub fn rustc_raw_entry_from_hash_unchecked(&mut self, hash: u64) -> RustcRawEntryRef<'_, K, V, S, A>
    {
        match self.table.find(hash, |_| true) {
            Some(elem) => RustcRawEntryRef::Occupied(RustcOccupiedEntryRef { hash, elem, map: self }),
            None => RustcRawEntryRef::Vacant(RustcRawVacantEntryRef { hash, map: self })
        }
    }
    
    /// get a raw entry from a borrow of a key. you can only insert into this if your key equals the query key.
    pub fn rustc_raw_entry_by_key<Q>(&mut self, key: &Q) -> RustcRawEntryRef<'_, K, V, S, A>
    where
        K: Borrow<Q>,
        Q: Hash + Eq
    {
        let hash = make_hash::<K, Q, S>(&self.hash_builder, key);
        match self.table.find(hash, move |x| key.eq(x.0.borrow())) {
            Some(elem) => RustcRawEntryRef::Occupied(RustcOccupiedEntryRef { hash, elem, map: self }),
            None => RustcRawEntryRef::Vacant(RustcRawVacantEntryRef { hash, map: self })
        }
    }
}

/// An entry which borrows its key from the collection when possible.
pub enum RustcEntryRef<'a, K, V, S, A = Global>
where
    A: Allocator + Clone,
{
    /// An occupied entry, which does not own a key.
    Occupied(RustcOccupiedEntryRef<'a, K, V, S, A>),

    /// A vacant entry.
    Vacant(RustcVacantEntryRef<'a, K, V, S, A>),
}

/// An entry which borrows its key from the collection when possible.
pub enum RustcRawEntryRef<'a, K, V, S, A = Global>
where
    A: Allocator + Clone,
{
    /// An occupied entry, which does not own a key.
    Occupied(RustcOccupiedEntryRef<'a, K, V, S, A>),

    /// A raw vacant entry which needs a key to insert.
    Vacant(RustcRawVacantEntryRef<'a, K, V, S, A>),
}

/// A view into an occupied entry in a `HashMap`.
/// It borrows it can be used to borrow a key and value from the map.
pub struct RustcOccupiedEntryRef<'a, K, V, S, A = Global>
where
    A: Allocator + Clone,
{
    hash: u64,
    elem: Bucket<(K, V)>,
    map: &'a mut HashMap<K, V, S, A>
}

/// A view into a vacant entry in a `HashMap`.
/// It is part of the [`RustcEntry`] enum.
/// 
/// This type already owns a key, and has hashed it.
pub struct RustcVacantEntryRef<'a, K, V, S, A = Global>
where
    A: Allocator + Clone,
{
    hash: u64,
    key: K,
    map: &'a mut HashMap<K, V, S, A>
}

/// A view into a vacant entry in a `HashMap`.
/// It does not own a key, and therefore must be provided one to insert
/// that matches the stored hash, and equals whatever produced it.
pub struct RustcRawVacantEntryRef<'a, K, V, S, A = Global>
where
    A: Allocator + Clone,
{
    hash: u64,
    map: &'a mut HashMap<K, V, S, A>
}

impl<'a, K, V, A: Allocator + Clone, S> RustcEntryRef<'a, K, V, S, A> {
    /// get the hash of the entry
    pub fn get_hash(&self) -> u64 {
        match self {
            Self::Occupied(o) => o.get_hash(),
            Self::Vacant(v) => v.get_hash(),
        }
    }

    /// convert back into a mutable reference to a HashMap
    pub fn into_collection_mut(self) -> &'a mut HashMap<K, V, S, A> {
        match self {
            Self::Occupied(o) => o.into_collection_mut(),
            Self::Vacant(v) => v.into_collection_mut(),
        }
    }
}

impl<'a, K, V, A: Allocator + Clone, S> RustcRawEntryRef<'a, K, V, S, A> {
    /// get the hash of the entry
    pub fn get_hash(&self) -> u64 {
        match self {
            Self::Occupied(o) => o.get_hash(),
            Self::Vacant(v) => v.get_hash(),
        }
    }

    /// convert back into a mutable reference to a HashMap
    pub fn into_collection_mut(self) -> &'a mut HashMap<K, V, S, A> {
        match self {
            Self::Occupied(o) => o.into_collection_mut(),
            Self::Vacant(v) => v.into_collection_mut(),
        }
    }
}

impl<'a, K, V, A: Allocator + Clone, S> RustcOccupiedEntryRef<'a, K, V, S, A> {
    /// get the hash of the entry.
    pub fn get_hash(&self) -> u64 {
        self.hash
    }

    /// convert back into a mutable reference to a HashMap.
    pub fn into_collection_mut(self) -> &'a mut HashMap<K, V, S, A> {
        self.map
    }

    /// get reference to the key in the entry.
    pub fn key(&self) -> &K {
        let (ref k, _) = unsafe { self.elem.as_ref() };
        k
    }

    /// get reference to the key in the entry, with the lifetime of the map itself.
    pub fn into_key(self) -> &'a K {
        let (ref k, _) = unsafe { self.elem.as_ref() };
        k
    }

    /// gets a mutable reference to the key in the entry.
    pub fn key_mut_unchecked(&mut self) -> &mut K {
        let (ref mut k, _) = unsafe { self.elem.as_mut() };
        k
    }

    pub fn into_key_mut_unchecked(self) -> &'a mut K {
        let (ref mut k, _) = unsafe { self.elem.as_mut() };
        k
    }

    pub fn get(&self) -> &V {
        let (_, ref v) = unsafe { self.elem.as_ref() };
        v
    }

    pub fn get_mut(&mut self) -> &mut V {
        let (_, ref mut v) = unsafe { self.elem.as_mut() };
        v
    }

    pub fn into_mut(self) -> &'a mut V {
        let (_, ref mut v) = unsafe { self.elem.as_mut() };
        v
    }

    pub fn get_key_value(&self) -> (&K, &V) {
        let (ref k, ref v) = unsafe { self.elem.as_ref() };
        (k, v)
    }

    pub fn get_key_value_mut(&mut self) -> (&K, &mut V) {
        let (ref k, ref mut v) = unsafe { self.elem.as_mut() };
        (k, v)
    }

    pub fn get_key_value_mut_unchecked(&mut self) -> (&mut K, &mut V) {
        let (ref mut k, ref mut v) = unsafe { self.elem.as_mut() };
        (k, v)
    }

    pub fn into_key_value(self) -> (&'a K, &'a mut V) {
        let (ref k, ref mut v) = unsafe { self.elem.as_mut() };
        (k, v)
    }

    pub fn into_key_value_unchecked(self) -> (&'a mut K, &'a mut V) {
        let (ref mut k, ref mut v) = unsafe { self.elem.as_mut() };
        (k, v)
    }

    /// replace a key if it hashes to the same thing as the old key
    pub fn replace_key(&mut self, key: K) -> Result<K, K>
    where
        S: BuildHasher,
        K: Hash,
    {
        let hash = make_insert_hash::<K, S>(&self.map.hash_builder, &key);
        if self.hash == hash {
            Ok(core::mem::replace(self.key_mut_unchecked(), key))
        } else {
            Err(key)
        }
    }

    pub fn replace_value(&mut self, value: V) -> V {
        core::mem::replace(self.get_mut(), value)
    }

    /// vacate the entry, returning a VacantEntry and a value.
    pub fn vacate(self) -> (RustcVacantEntryRef<'a, K, V, S, A>, V) {
        todo!()
    }

    /// vacate the entry, returning a RawVacantEntry and a key-value pair.
    pub fn vacate_raw(self) -> (RustcRawVacantEntryRef<'a, K, V, S, A>, K, V) {
        todo!()
    }

    pub fn remove(self) -> V {
        todo!()
    }

    pub fn remove_key_value(self) -> (K, V) {
        todo!()
    }
}

impl<'a, K, V, A: Allocator + Clone, S> RustcVacantEntryRef<'a, K, V, S, A> {
    /// get the hash of the entry
    pub fn get_hash(&self) -> u64 {
        self.hash
    }

    /// convert back into a mutable reference to a HashMap
    pub fn into_collection_mut(self) -> &'a mut HashMap<K, V, S, A> {
        self.map
    }

    /// Gets a reference to the key that would be used when inserting a value
    /// through the `RustcVacantEntry`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMap;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// assert_eq!(map.rustc_entry("poneyland").key(), &"poneyland");
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key(&self) -> &K {
        &self.key
    }

    /// Take ownership of the key.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMap;
    /// use hashbrown::hash_map::RustcEntry;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    ///
    /// if let RustcEntry::Vacant(v) = map.rustc_entry("poneyland") {
    ///     v.into_key();
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_key(self) -> K {
        self.key
    }

    /// Sets the value of the entry with the RustcVacantEntry's key,
    /// and returns a mutable reference to it.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMap;
    /// use hashbrown::hash_map::RustcEntry;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    ///
    /// if let RustcEntry::Vacant(o) = map.rustc_entry("poneyland") {
    ///     o.insert(37);
    /// }
    /// assert_eq!(map["poneyland"], 37);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert(self, value: V) -> &'a mut V {
        unsafe {
            let bucket = self.map.table.insert_no_grow(self.hash, (self.key, value));
            &mut bucket.as_mut().1
        }
    }

    /// insert `value` into the collection using the owned key, creating an OccupiedEntryRef.
    /// this replaces the insert_entry method, and does not need to clone keys ever.
    pub fn occupy(self, value: V) -> RustcOccupiedEntryRef<'a, K, V, S, A> {
        let bucket = unsafe { self.map.table.insert_no_grow(self.hash, (self.key, value)) };
        RustcOccupiedEntryRef {
            hash: self.hash,
            elem: bucket,
            map: self.map,
        }
    }
    
    /// take the key, stepping down to a `RawVacantEntry`
    pub fn into_raw(self) -> (RustcRawVacantEntryRef<'a, K, V, S, A>, K) {
        todo!()
    }
}

impl<'a, K, V, A: Allocator + Clone, S> RustcRawVacantEntryRef<'a, K, V, S, A> {
    /// get the hash of the entry
    pub fn get_hash(&self) -> u64 {
        self.hash
    }

    /// convert back into a mutable reference to a HashMap
    pub fn into_collection_mut(self) -> &'a mut HashMap<K, V, S, A> {
        self.map
    }

    /// insert `key` into the Self, creating a regular VacantEntry if it hashes to the same value this entry was created with.
    pub fn into_vacant_entry(self, key: K) -> Result<RustcVacantEntryRef<'a, K, V, S, A>, K>
    where
        S: BuildHasher,
        K: Hash,
    {
        let hash = make_insert_hash::<K, S>(&self.map.hash_builder, &key);
        if self.hash == hash {
            Ok(self.into_vacant_entry_unchecked(key))
        } else {
            Err(key)
        }
    }
        
    /// insert `key` into the Self, creating a regular VacantEntry. This assumes `key` hashes to the value this entry was created with.
    pub fn into_vacant_entry_unchecked(self, key: K) -> RustcVacantEntryRef<'a, K, V, S, A> {
        let Self { hash, map, } = self;
        RustcVacantEntryRef { hash, key, map }
    }

    /// insert `(key, value)` into the collection, creating an OccupiedEntryRef if it hashes to the same value this entry was created with.
    pub fn occupy(self, key: K, value: V) -> Result<RustcOccupiedEntryRef<'a, K, V, S, A>, (K, V)>
    where
        S: BuildHasher,
        K: Hash,
    {
        let hash = make_insert_hash::<K, S>(&self.map.hash_builder, &key);
        if self.hash == hash {
            Ok(self.occupy_unchecked(key, value))
        } else {
            Err((key, value))
        }
    }

    /// insert `(key, value)` into the collection, creating an OccupiedEntryRef. This assumes `key` hashes to the value this entry was created with.
    pub fn occupy_unchecked(self, key: K, value: V) -> RustcOccupiedEntryRef<'a, K, V, S, A> {
        todo!()
    }
}
