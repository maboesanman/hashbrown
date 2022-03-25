use self::RustcEntry::*;
use crate::hash_map::DefaultHashBuilder;
use crate::map::{make_insert_hash, Drain, HashMap, IntoIter, Iter, IterMut};
use crate::raw::{Allocator, Bucket, Global, RawTable};
use core::borrow::Borrow;
use core::fmt::{self, Debug};
use core::hash::{BuildHasher, Hash};
use core::mem;

impl<K, V, S, A> HashMap<K, V, S, A>
where
    K: Eq + Hash,
    S: BuildHasher,
    A: Allocator + Clone,
{
    /// Gets the given key's corresponding entry in the map for in-place manipulation.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMap;
    ///
    /// let mut letters = HashMap::new();
    ///
    /// for ch in "a short treatise on fungi".chars() {
    ///     let counter = letters.rustc_entry(ch).or_insert(0);
    ///     *counter += 1;
    /// }
    ///
    /// assert_eq!(letters[&'s'], 2);
    /// assert_eq!(letters[&'t'], 3);
    /// assert_eq!(letters[&'u'], 1);
    /// assert_eq!(letters.get(&'y'), None);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn rustc_entry(&mut self, key: K) -> RustcEntry<'_, K, V, A, S> {
        let hash = make_insert_hash(&self.hash_builder, &key);
        if let Some(elem) = self.table.find(hash, |q| q.0.eq(&key)) {
            RustcEntry::Occupied(RustcOccupiedEntry {
                key: Some(key),
                elem,
                map: self,
            })
        } else {
            // Ideally we would put this in VacantEntry::insert, but Entry is not
            // generic over the BuildHasher and adding a generic parameter would be
            // a breaking change.
            self.reserve(1);

            RustcEntry::Vacant(RustcVacantEntry {
                hash,
                key,
                map: self,
            })
        }
    }

    /// get an EntryRef, cloning the key if vacant.
    pub fn rustc_entry_ref<Q>(&mut self, key: &Q) -> RustcEntryRef<'_, K, V, A, S>
    where
        Q: Borrow<K> + Hash + Eq,
        K: Clone,
    {
        todo!()
    }

    /// get an occupied entry if it exists.
    pub fn rustc_occupied_entry_ref<Q>(&mut self, key: &Q) -> Option<RustcOccupiedEntryRef<'_, K, V, A, S>>
    where
        Q: Borrow<K> + Hash + Eq
    {
        todo!()
    }
    
    /// get a vacant entry. return the key if it's occupied.
    pub fn rustc_vacant_entry(&mut self, key: K) -> Result<RustcVacantEntry<'_, K, V, A, S>, K> {
        todo!()
    }
    
    /// get a raw entry from a hash and a matcher function.
    pub fn rustc_raw_entry_from_hash<F>(&mut self, hash: u64, is_match: F) -> RustcRawEntry<'_, K, V, A, S>
    where
        for<'b> F: FnMut(&'b K) -> bool
    {
        todo!()
    }
    
    /// get a raw entry from a hash and assume it matches.
    pub fn rustc_raw_entry_from_hash_unchecked(&mut self, hash: u64) -> RustcRawEntry<'_, K, V, A, S>
    {
        todo!()
    }
    
    /// get a raw entry from a borrow of a key.
    pub fn rustc_raw_entry_by_key<Q>(&mut self, key: &Q) -> RustcRawEntry<'_, K, V, A, S>
    where
        Q: Borrow<K> + Hash + Eq
    {
        todo!()
    }
}

/// A view into a single entry in a map, which may either be vacant or occupied.
///
/// This `enum` is constructed from the [`entry`] method on [`HashMap`].
///
/// [`HashMap`]: struct.HashMap.html
/// [`entry`]: struct.HashMap.html#method.rustc_entry
pub enum RustcEntry<'a, K, V, A = Global, S = DefaultHashBuilder>
where
    A: Allocator + Clone,
{
    /// An occupied entry.
    Occupied(RustcOccupiedEntry<'a, K, V, A, S>),

    /// A vacant entry.
    Vacant(RustcVacantEntry<'a, K, V, A, S>),
}

impl<K: Debug, V: Debug, A: Allocator + Clone, S: BuildHasher> Debug for RustcEntry<'_, K, V, A, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Vacant(ref v) => f.debug_tuple("Entry").field(v).finish(),
            Occupied(ref o) => f.debug_tuple("Entry").field(o).finish(),
        }
    }
}

/// An entry which borrows its key from the collection when possible.
pub enum RustcEntryRef<'a, K, V, A = Global,  S = DefaultHashBuilder>
where
    A: Allocator + Clone,
{
    /// An occupied entry, which does not own a key.
    Occupied(RustcOccupiedEntryRef<'a, K, V, A, S>),

    /// A vacant entry.
    Vacant(RustcVacantEntry<'a, K, V, A, S>),
}

/// An entry which borrows its key from the collection when possible.
pub enum RustcRawEntry<'a, K, V, A = Global,  S = DefaultHashBuilder>
where
    A: Allocator + Clone,
{
    /// An occupied entry, which does not own a key.
    Occupied(RustcOccupiedEntryRef<'a, K, V, A, S>),

    /// A raw vacant entry which needs a key to insert.
    Vacant(RustcRawVacantEntry<'a, K, V, A, S>),
}

/// A view into an occupied entry in a `HashMap`.
/// It is part of the [`RustcEntry`] enum.
///
/// [`RustcEntry`]: enum.RustcEntry.html
pub struct RustcOccupiedEntry<'a, K, V, A = Global,  S = DefaultHashBuilder>
where
    A: Allocator + Clone,
{
    key: Option<K>,
    elem: Bucket<(K, V)>,
    map: &'a mut HashMap<K, V, S, A>
}

unsafe impl<K, V, S, A> Send for RustcOccupiedEntry<'_, K, V, A, S>
where
    K: Send,
    V: Send,
    S: BuildHasher,
    A: Allocator + Clone + Send,
{
}
unsafe impl<K, V, S, A> Sync for RustcOccupiedEntry<'_, K, V, A, S>
where
    K: Sync,
    V: Sync,
    S: BuildHasher,
    A: Allocator + Clone + Sync,
{
}

impl<K: Debug, V: Debug, S: BuildHasher, A: Allocator + Clone> Debug for RustcOccupiedEntry<'_, K, V, A, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OccupiedEntry")
            .field("key", self.key())
            .field("value", self.get())
            .finish()
    }
}

/// A view into an occupied entry in a `HashMap`.
/// It borrows it can be used to borrow a key and value from the map.
pub struct RustcOccupiedEntryRef<'a, K, V, A = Global,  S = DefaultHashBuilder>
where
    A: Allocator + Clone,
{
    hash: u64,
    elem: Bucket<(K, V)>,
    map: &'a mut HashMap<K, V, S, A>
}

/// A view into a vacant entry in a `HashMap`.
/// It is part of the [`RustcEntry`] enum.
pub struct RustcVacantEntry<'a, K, V, A = Global,  S = DefaultHashBuilder>
where
    A: Allocator + Clone,
{
    hash: u64,
    key: K,
    map: &'a mut HashMap<K, V, S, A>
}

impl<K: Debug, V, S, A: Allocator + Clone> Debug for RustcVacantEntry<'_, K, V, A, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("VacantEntry").field(self.key()).finish()
    }
}

/// A view into a vacant entry in a `HashMap`.
/// It does not own a key, and therefore must be provided one to insert.
pub struct RustcRawVacantEntry<'a, K, V, A = Global,  S = DefaultHashBuilder>
where
    A: Allocator + Clone,
{
    hash: u64,
    map: &'a mut HashMap<K, V, S, A>
}

impl<'a, K, V, A: Allocator + Clone, S> RustcEntry<'a, K, V, A, S> {
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
    /// Sets the value of the entry, and returns a RustcOccupiedEntry.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMap;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// let entry = map.entry("horseyland").insert(37);
    ///
    /// assert_eq!(entry.key(), &"horseyland");
    /// ```
    pub fn insert(self, value: V) -> RustcOccupiedEntry<'a, K, V, A, S> {
        match self {
            Vacant(entry) => entry.insert_entry(value),
            Occupied(mut entry) => {
                entry.insert(value);
                entry
            }
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty, and returns
    /// a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMap;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    ///
    /// map.rustc_entry("poneyland").or_insert(3);
    /// assert_eq!(map["poneyland"], 3);
    ///
    /// *map.rustc_entry("poneyland").or_insert(10) *= 2;
    /// assert_eq!(map["poneyland"], 6);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn or_insert(self, default: V) -> &'a mut V
    where
        K: Hash,
    {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMap;
    ///
    /// let mut map: HashMap<&str, String> = HashMap::new();
    /// let s = "hoho".to_string();
    ///
    /// map.rustc_entry("poneyland").or_insert_with(|| s);
    ///
    /// assert_eq!(map["poneyland"], "hoho".to_string());
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V
    where
        K: Hash,
    {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => entry.insert(default()),
        }
    }

    /// Returns a reference to this entry's key.
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
        match *self {
            Occupied(ref entry) => entry.key(),
            Vacant(ref entry) => entry.key(),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMap;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    ///
    /// map.rustc_entry("poneyland")
    ///    .and_modify(|e| { *e += 1 })
    ///    .or_insert(42);
    /// assert_eq!(map["poneyland"], 42);
    ///
    /// map.rustc_entry("poneyland")
    ///    .and_modify(|e| { *e += 1 })
    ///    .or_insert(42);
    /// assert_eq!(map["poneyland"], 43);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: FnOnce(&mut V),
    {
        match self {
            Occupied(mut entry) => {
                f(entry.get_mut());
                Occupied(entry)
            }
            Vacant(entry) => Vacant(entry),
        }
    }
}

impl<'a, K, V: Default, S, A: Allocator + Clone> RustcEntry<'a, K, V, A, S> {
    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// # fn main() {
    /// use hashbrown::HashMap;
    ///
    /// let mut map: HashMap<&str, Option<u32>> = HashMap::new();
    /// map.rustc_entry("poneyland").or_default();
    ///
    /// assert_eq!(map["poneyland"], None);
    /// # }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn or_default(self) -> &'a mut V
    where
        K: Hash,
    {
        match self {
            Occupied(entry) => entry.into_mut(),
            Vacant(entry) => entry.insert(Default::default()),
        }
    }
}

impl<'a, K, V, A: Allocator + Clone, S> RustcEntryRef<'a, K, V, A, S> {
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

impl<'a, K, V, A: Allocator + Clone, S> RustcRawEntry<'a, K, V, A, S> {
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

impl<'a, K, V, A: Allocator + Clone, S> RustcOccupiedEntry<'a, K, V, A, S> {
    /// get the hash of the entry
    pub fn get_hash(&self) -> u64 {
        todo!()
    }

    /// convert back into a mutable reference to a HashMap
    pub fn into_collection_mut(self) -> &'a mut HashMap<K, V, S, A> {
        self.map
    }
    /// Gets a reference to the key in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMap;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// map.rustc_entry("poneyland").or_insert(12);
    /// assert_eq!(map.rustc_entry("poneyland").key(), &"poneyland");
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn key(&self) -> &K {
        unsafe { &self.elem.as_ref().0 }
    }

    /// Take the ownership of the key and value from the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMap;
    /// use hashbrown::hash_map::RustcEntry;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// map.rustc_entry("poneyland").or_insert(12);
    ///
    /// if let RustcEntry::Occupied(o) = map.rustc_entry("poneyland") {
    ///     // We delete the entry from the map.
    ///     o.remove_entry();
    /// }
    ///
    /// assert_eq!(map.contains_key("poneyland"), false);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove_entry(self) -> (K, V) {
        unsafe { self.map.table.remove(self.elem) }
    }

    /// Gets a reference to the value in the entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMap;
    /// use hashbrown::hash_map::RustcEntry;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// map.rustc_entry("poneyland").or_insert(12);
    ///
    /// if let RustcEntry::Occupied(o) = map.rustc_entry("poneyland") {
    ///     assert_eq!(o.get(), &12);
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn get(&self) -> &V {
        unsafe { &self.elem.as_ref().1 }
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the `RustcOccupiedEntry` which may outlive the
    /// destruction of the `RustcEntry` value, see [`into_mut`].
    ///
    /// [`into_mut`]: #method.into_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMap;
    /// use hashbrown::hash_map::RustcEntry;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// map.rustc_entry("poneyland").or_insert(12);
    ///
    /// assert_eq!(map["poneyland"], 12);
    /// if let RustcEntry::Occupied(mut o) = map.rustc_entry("poneyland") {
    ///     *o.get_mut() += 10;
    ///     assert_eq!(*o.get(), 22);
    ///
    ///     // We can use the same RustcEntry multiple times.
    ///     *o.get_mut() += 2;
    /// }
    ///
    /// assert_eq!(map["poneyland"], 24);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn get_mut(&mut self) -> &mut V {
        unsafe { &mut self.elem.as_mut().1 }
    }

    /// Converts the RustcOccupiedEntry into a mutable reference to the value in the entry
    /// with a lifetime bound to the map itself.
    ///
    /// If you need multiple references to the `RustcOccupiedEntry`, see [`get_mut`].
    ///
    /// [`get_mut`]: #method.get_mut
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMap;
    /// use hashbrown::hash_map::RustcEntry;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// map.rustc_entry("poneyland").or_insert(12);
    ///
    /// assert_eq!(map["poneyland"], 12);
    /// if let RustcEntry::Occupied(o) = map.rustc_entry("poneyland") {
    ///     *o.into_mut() += 10;
    /// }
    ///
    /// assert_eq!(map["poneyland"], 22);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn into_mut(self) -> &'a mut V {
        unsafe { &mut self.elem.as_mut().1 }
    }

    /// Sets the value of the entry, and returns the entry's old value.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMap;
    /// use hashbrown::hash_map::RustcEntry;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// map.rustc_entry("poneyland").or_insert(12);
    ///
    /// if let RustcEntry::Occupied(mut o) = map.rustc_entry("poneyland") {
    ///     assert_eq!(o.insert(15), 12);
    /// }
    ///
    /// assert_eq!(map["poneyland"], 15);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert(&mut self, mut value: V) -> V {
        let old_value = self.get_mut();
        mem::swap(&mut value, old_value);
        value
    }

    /// Takes the value out of the entry, and returns it.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::HashMap;
    /// use hashbrown::hash_map::RustcEntry;
    ///
    /// let mut map: HashMap<&str, u32> = HashMap::new();
    /// map.rustc_entry("poneyland").or_insert(12);
    ///
    /// if let RustcEntry::Occupied(o) = map.rustc_entry("poneyland") {
    ///     assert_eq!(o.remove(), 12);
    /// }
    ///
    /// assert_eq!(map.contains_key("poneyland"), false);
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn remove(self) -> V {
        self.remove_entry().1
    }

    /// Replaces the entry, returning the old key and value. The new key in the hash map will be
    /// the key used to create this entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::hash_map::{RustcEntry, HashMap};
    /// use std::rc::Rc;
    ///
    /// let mut map: HashMap<Rc<String>, u32> = HashMap::new();
    /// map.insert(Rc::new("Stringthing".to_string()), 15);
    ///
    /// let my_key = Rc::new("Stringthing".to_string());
    ///
    /// if let RustcEntry::Occupied(entry) = map.rustc_entry(my_key) {
    ///     // Also replace the key with a handle to our other key.
    ///     let (old_key, old_value): (Rc<String>, u32) = entry.replace_entry(16);
    /// }
    ///
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_entry(self, value: V) -> (K, V) {
        let entry = unsafe { self.elem.as_mut() };

        let old_key = mem::replace(&mut entry.0, self.key.unwrap());
        let old_value = mem::replace(&mut entry.1, value);

        (old_key, old_value)
    }

    /// Replaces the key in the hash map with the key used to create this entry.
    ///
    /// # Examples
    ///
    /// ```
    /// use hashbrown::hash_map::{RustcEntry, HashMap};
    /// use std::rc::Rc;
    ///
    /// let mut map: HashMap<Rc<String>, u32> = HashMap::new();
    /// let mut known_strings: Vec<Rc<String>> = Vec::new();
    ///
    /// // Initialise known strings, run program, etc.
    ///
    /// reclaim_memory(&mut map, &known_strings);
    ///
    /// fn reclaim_memory(map: &mut HashMap<Rc<String>, u32>, known_strings: &[Rc<String>] ) {
    ///     for s in known_strings {
    ///         if let RustcEntry::Occupied(entry) = map.rustc_entry(s.clone()) {
    ///             // Replaces the entry's key with our version of it in `known_strings`.
    ///             entry.replace_key();
    ///         }
    ///     }
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn replace_key(self) -> K {
        let entry = unsafe { self.elem.as_mut() };
        mem::replace(&mut entry.0, self.key.unwrap())
    }
}

impl<'a, K, V, A: Allocator + Clone, S> RustcOccupiedEntryRef<'a, K, V, A, S> {
    /// get the hash of the entry
    pub fn get_hash(&self) -> u64 {
        self.hash
    }

    /// convert back into a mutable reference to a HashMap
    pub fn into_collection_mut(self) -> &'a mut HashMap<K, V, S, A> {
        self.map
    }

    /// get reference to the key
    pub fn key(&self) -> &K {
        todo!()
    }

    /// convert to references into the collection
    pub fn into_entry(self) -> (&'a K, &'a mut V) {
        todo!()
    }

    /// convert to references into the collection
    pub fn into_key_mut_entry(self) -> (&'a mut K, &'a mut V) {
        todo!()
    }

    /// vacate the entry, returning a VacantEntry and a value.
    pub fn vacate(self) -> (RustcVacantEntry<'a, K, V, A, S>, V) {
        todo!()
    }

    /// vacate the entry, returning a RawVacantEntry and a key-value pair.
    pub fn vacate_raw(self) -> (RustcRawVacantEntry<'a, K, V, A, S>, K, V) {
        todo!()
    }
}

impl<'a, K, V, A: Allocator + Clone, S> RustcVacantEntry<'a, K, V, A, S> {
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

    /// Sets the value of the entry with the RustcVacantEntry's key,
    /// and returns a RustcOccupiedEntry.
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
    ///     let o = v.insert_entry(37);
    ///     assert_eq!(o.get(), &37);
    /// }
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn insert_entry(self, value: V) -> RustcOccupiedEntry<'a, K, V, A, S> {
        let bucket = unsafe { self.map.table.insert_no_grow(self.hash, (self.key, value)) };
        RustcOccupiedEntry {
            key: None,
            elem: bucket,
            map: self.map,
        }
    }

    /// insert `value` into the collection using the owned key, creating an OccupiedEntryRef.
    /// this replaces the insert_entry method, and does not need to clone keys ever.
    pub fn occupy(self, value: V) -> RustcOccupiedEntryRef<'a, K, V, A, S> {
        todo!()
    }
    
    /// take the key, stepping down to a `RawVacantEntry`
    pub fn into_raw(self) -> (RustcRawVacantEntry<'a, K, V, A, S>, K) {
        todo!()
    }
}

impl<'a, K, V, A: Allocator + Clone, S> RustcRawVacantEntry<'a, K, V, A, S> {
    /// get the hash of the entry
    pub fn get_hash(&self) -> u64 {
        self.hash
    }

    /// convert back into a mutable reference to a HashMap
    pub fn into_collection_mut(self) -> &'a mut HashMap<K, V, S, A> {
        self.map
    }

    /// insert `key` into the Self, creating a regular VacantEntry if it hashes to the same value this entry was created with.
    pub fn into_vacant_entry(self, key: K) -> Result<RustcVacantEntry<'a, K, V, A, S>, K> {
        todo!()
    }
        
    /// insert `key` into the Self, creating a regular VacantEntry. This assumes `key` hashes to the value this entry was created with.
    pub fn into_vacant_entry_unchecked(self, key: K) -> RustcVacantEntry<'a, K, V, A, S> {
        let Self {
            hash,
            map,
        } = self;
        RustcVacantEntry { hash, key, map }
    }

    /// insert `(key, value)` into the collection, creating an OccupiedEntryRef if it hashes to the same value this entry was created with.
    pub fn occupy(self, key: K, value: V) -> Result<RustcOccupiedEntryRef<'a, K, V, A, S>, (K, V)> {
        todo!()
    }

    /// insert `(key, value)` into the collection, creating an OccupiedEntryRef. This assumes `key` hashes to the value this entry was created with.
    pub fn occupy_unchecked(self, key: K, value: V) -> RustcOccupiedEntryRef<'a, K, V, A, S> {
        todo!()
    }
}

impl<K, V> IterMut<'_, K, V> {
    /// Returns a iterator of references over the remaining items.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn rustc_iter(&self) -> Iter<'_, K, V> {
        self.iter()
    }
}

impl<K, V> IntoIter<K, V> {
    /// Returns a iterator of references over the remaining items.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn rustc_iter(&self) -> Iter<'_, K, V> {
        self.iter()
    }
}

impl<K, V> Drain<'_, K, V> {
    /// Returns a iterator of references over the remaining items.
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn rustc_iter(&self) -> Iter<'_, K, V> {
        self.iter()
    }
}
