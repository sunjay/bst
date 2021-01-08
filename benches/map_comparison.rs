use std::borrow::Borrow;
use std::hash::Hash;
use std::collections::{BTreeMap, HashMap};

use rand::prelude::*;
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};

use bst::BSTMap;

trait Map<K, V> {
    fn new() -> Self;

    fn len(&self) -> usize;

    fn get<Q>(&self, key: &Q) -> Option<&V>
        where K: Borrow<Q>,
              Q: Ord + Hash + Eq + ?Sized;

    fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
        where K: Borrow<Q>,
              Q: Ord + Hash + Eq + ?Sized;

    fn insert(&mut self, key: K, value: V) -> Option<V>;

    fn remove<Q>(&mut self, key: &Q) -> Option<V>
        where K: Borrow<Q>,
              Q: Ord + Hash + Eq + ?Sized;
}

macro_rules! impl_map {
    ($name:ident, $bound:ident $(+ $other_bound:ident)*) => {
        impl<K, V> Map<K, V> for $name<K, V>
            where K: $bound $(+ $other_bound)*,
        {
            fn new() -> Self {
                $name::new()
            }

            fn len(&self) -> usize {
                $name::len(self)
            }

            fn get<Q>(&self, key: &Q) -> Option<&V>
                where K: Borrow<Q>,
                      Q: Ord + Hash + Eq + ?Sized
            {
                $name::get(self, key)
            }

            fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
                where K: Borrow<Q>,
                      Q: Ord + Hash + Eq + ?Sized
            {
                $name::get_mut(self, key)
            }

            fn insert(&mut self, key: K, value: V) -> Option<V> {
                $name::insert(self, key, value)
            }

            fn remove<Q>(&mut self, key: &Q) -> Option<V>
                where K: Borrow<Q>,
                      Q: Ord + Hash + Eq + ?Sized
            {
                $name::remove(self, key)
            }
        }
    };
}

impl_map!(HashMap, Hash + Eq);
impl_map!(BTreeMap, Ord);
impl_map!(BSTMap, Ord);

#[derive(Debug, Clone)]
struct Keys {
    keys: Vec<i64>,
}

impl Keys {
    /// Deterministically generates a set of at least `nkeys` values
    ///
    /// All values are guaranteed to be unique and ordered randomly.
    pub fn generate(nkeys: u32) -> Self {
        // Want to spread keys out so we generate interesting trees/tables.
        // Trying not to generate consecutive keys or keys that are strictly
        // increasing in magnitude.

        let mut keys = Vec::new();

        let n = nkeys as i64;
        for i in 0..n {
            // [0..n] - n/2 = [-n/2..n/2]
            // [-n/2..n/2] * 4 = [-4n/2..4n/2]
            // Multiply by 4 so that numbers aren't consecutive
            let key = (i - n/2) * 10;
            keys.push(key);
        }

        // Use seed to make this deterministic
        let mut rng = StdRng::seed_from_u64(45930923092);
        // Shuffle to ensure that keys are in a uniformly random order
        keys.shuffle(&mut rng);

        Self {keys}
    }

    pub fn get(&self, key_i: i64) -> i64 {
        // Make sure index is >= 0
        let index = key_i.max(0);
        self.keys[index as usize]
    }
}

fn slice_max<T: Copy + Ord>(data: &[T]) -> T {
    data.iter().max().copied().expect("bug: slice was empty")
}

/// Runs many consecutive inserts on a map
fn benchmark_inserts<M: Map<i64, usize>>(keys: &Keys, inserts: usize) -> M {
    let mut map = M::new();

    for key_i in 0..inserts {
        black_box(map.insert(keys.get(key_i as i64), key_i));
    }

    map
}

/// Setup function for benchmark_gets
fn setup_benchmark_gets<M: Map<i64, usize>>(keys: &Keys, gets: usize) -> M {
    let mut map = M::new();

    for key_i in 0..gets {
        black_box(map.insert(keys.get(key_i as i64), key_i));
    }

    map
}

/// Runs many consecutive get operations on a map
fn benchmark_gets<M: Map<i64, usize>>(keys: &Keys, map: &mut M, gets: usize) {
    for i in 0..gets {
        // Get keys in the opposite order to how they were inserted
        let key_i = gets - i - 1;
        let key = keys.get(key_i as i64);
        black_box(map.get(&key));
        black_box(map.get_mut(&key));
    }
}

/// Runs a bunch of operations on a map
fn benchmark_map_ops<M: Map<i64, usize>>(keys: &Keys, steps: usize) -> M {
    const MAX_INSERTS: usize = 5;
    const MAX_GETS: usize = 3;
    // const MAX_REMOVES: usize = 2;

    let mut map = M::new();

    let mut key_i = 0;
    for i in 0..steps {
        // Perform a few insertions
        let insertions = i % MAX_INSERTS;
        // Loop always runs at least once
        for j in 0..=insertions {
            let key = keys.get(key_i);
            key_i += 1;
            black_box(map.insert(key, i + j));
        }

        // Overwrite a previous insertion
        let key = keys.get(key_i - 1);
        black_box(map.insert(key, 0));

        // Try to get and update several values
        let gets = MAX_GETS - (i % MAX_GETS);
        for j in 0..gets {
            let key = keys.get(key_i - j as i64);
            let value = match map.get(&key) {
                Some(value) => *value,
                None => continue, // ignore
            };
            match map.get_mut(&key) {
                Some(val) => *val = value * 2,
                None => continue, // ignore
            }
        }

        //TODO: Uncomment this when `BSTMap::remove` is implemented
        // Remove several values
        // let removes = MAX_REMOVES - (i % MAX_REMOVES);
        // for j in 0..removes {
        //     let key = make_key(key_i - j as i64);
        //     black_box(map.remove(&key));
        // }
    }

    map
}

pub fn bench_map_insert(c: &mut Criterion) {
    const INSERTS: &[usize] = &[50, 100, 500, 1000, 2000];

    let keys = Keys::generate(slice_max(INSERTS) as u32);

    let mut group = c.benchmark_group("insert");
    for inserts in INSERTS {
        group.bench_with_input(BenchmarkId::new("HashMap", inserts), inserts, |b, &inserts| {
            b.iter(|| benchmark_inserts::<HashMap<i64, usize>>(&keys, inserts))
        });
        group.bench_with_input(BenchmarkId::new("BTreeMap", inserts), inserts, |b, &inserts| {
            b.iter(|| benchmark_inserts::<BTreeMap<i64, usize>>(&keys, inserts))
        });
        group.bench_with_input(BenchmarkId::new("BSTMap", inserts), inserts, |b, &inserts| {
            b.iter(|| benchmark_inserts::<BSTMap<i64, usize>>(&keys, inserts))
        });
    }
    group.finish();
}

pub fn bench_map_get(c: &mut Criterion) {
    const GETS: &[usize] = &[50, 100, 500, 1000, 2000];

    let keys = Keys::generate(slice_max(GETS) as u32);

    let mut group = c.benchmark_group("get");
    for gets in GETS {
        group.bench_with_input(BenchmarkId::new("HashMap", gets), gets, |b, &gets| {
            let mut map = setup_benchmark_gets(&keys, gets);
            b.iter(|| benchmark_gets::<HashMap<i64, usize>>(&keys, &mut map, gets))
        });
        group.bench_with_input(BenchmarkId::new("BTreeMap", gets), gets, |b, &gets| {
            let mut map = setup_benchmark_gets(&keys, gets);
            b.iter(|| benchmark_gets::<BTreeMap<i64, usize>>(&keys, &mut map, gets))
        });
        group.bench_with_input(BenchmarkId::new("BSTMap", gets), gets, |b, &gets| {
            let mut map = setup_benchmark_gets(&keys, gets);
            b.iter(|| benchmark_gets::<BSTMap<i64, usize>>(&keys, &mut map, gets))
        });
    }
    group.finish();
}

pub fn bench_map_ops(c: &mut Criterion) {
    const STEPS: &[usize] = &[50, 100, 1000, 2000, 4000];

    // Using (max * 5) because we do up to `MAX_INSERTS` inserts per step
    let keys = Keys::generate(slice_max(STEPS) as u32 * 5);

    let mut group = c.benchmark_group("map operations");
    for steps in STEPS {
        group.bench_with_input(BenchmarkId::new("HashMap", steps), steps, |b, &steps| {
            b.iter(|| benchmark_map_ops::<HashMap<i64, usize>>(&keys, steps))
        });
        group.bench_with_input(BenchmarkId::new("BTreeMap", steps), steps, |b, &steps| {
            b.iter(|| benchmark_map_ops::<BTreeMap<i64, usize>>(&keys, steps))
        });
        group.bench_with_input(BenchmarkId::new("BSTMap", steps), steps, |b, &steps| {
            b.iter(|| benchmark_map_ops::<BSTMap<i64, usize>>(&keys, steps))
        });
    }
    group.finish();
}

criterion_group!(benches,
    bench_map_insert,
    bench_map_get,
    bench_map_ops,
);

criterion_main!(benches);
