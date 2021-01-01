use std::borrow::Borrow;
use std::hash::Hash;
use std::collections::{BTreeMap, HashMap};

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

// Generates a key for the map
//
// Note that the keys returned are not guaranteed to be unique, but will be
// largely unique.
fn make_key(i: i64) -> i64 {
    // Make sure i >= 0
    let i = i.max(0);

    // Want to spread keys out so we generate interesting trees/tables.
    // Trying not to generate consecutive keys or keys that are strictly
    // increasing in magnitude.

    // Since i >= 0, i % 3 = 0, 1, or 2
    // So 2/3 of numbers will be positive, 1/3 will be negative
    let sign = if i % 3 >= 1 { 1 } else { -1 };

    // Since i >= 0, i % 6 = 0, 1, 2, 3, 4, or 5
    // So 2/6 of numbers divided by 1 (no change)
    //    2/6 of numbers divided by 3
    //    2/6 of numbers divided by 6
    let divisor = match i % 6 {
        0 | 1 => 1,
        2 | 4 => 3,
        3 | 5 => 6,
        _ => unreachable!(),
    };

    sign * (i + 1) * 4 / divisor
}

/// Runs many consecutive inserts on a map
fn benchmark_inserts<M: Map<i64, usize>>(inserts: usize) -> M {
    let mut map = M::new();

    for key_i in 0..inserts {
        black_box(map.insert(make_key(key_i as i64), key_i));
    }

    map
}

/// Setup function for benchmark_gets
fn setup_benchmark_gets<M: Map<i64, usize>>(gets: usize) -> M {
    let mut map = M::new();

    for key_i in 0..gets {
        black_box(map.insert(make_key(key_i as i64), key_i));
    }

    map
}

/// Runs many consecutive get operations on a map
fn benchmark_gets<M: Map<i64, usize>>(map: &mut M, gets: usize) {
    for i in 0..gets {
        // Get keys in the opposite order to how they were inserted
        let key_i = gets - i - 1;
        let key = make_key(key_i as i64);
        black_box(map.get(&key));
        black_box(map.get_mut(&key));
    }
}

/// Runs a bunch of operations on a map
fn benchmark_map_ops<M: Map<i64, usize>>(steps: usize) -> M {
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
            let key = make_key(key_i);
            key_i += 1;
            black_box(map.insert(key, i + j));
        }

        // Overwrite a previous insertion
        let key = make_key(key_i - 1);
        black_box(map.insert(key, 0));

        // Try to get and update several values
        let gets = MAX_GETS - (i % MAX_GETS);
        for j in 0..gets {
            let key = make_key(key_i - j as i64);
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

pub fn bench_inserts(c: &mut Criterion) {
    const INSERTS: &[usize] = &[50, 100, 500, 1000, 2000];

    let mut group = c.benchmark_group("insert");
    for inserts in INSERTS {
        group.bench_with_input(BenchmarkId::new("HashMap", inserts), inserts, |b, &inserts| {
            b.iter(|| benchmark_inserts::<HashMap<i64, usize>>(inserts))
        });
        group.bench_with_input(BenchmarkId::new("BTreeMap", inserts), inserts, |b, &inserts| {
            b.iter(|| benchmark_inserts::<BTreeMap<i64, usize>>(inserts))
        });
        group.bench_with_input(BenchmarkId::new("BSTMap", inserts), inserts, |b, &inserts| {
            b.iter(|| benchmark_inserts::<BSTMap<i64, usize>>(inserts))
        });
    }
    group.finish();
}

pub fn bench_gets(c: &mut Criterion) {
    const GETS: &[usize] = &[50, 100, 500, 1000, 2000];

    let mut group = c.benchmark_group("get");
    for gets in GETS {
        group.bench_with_input(BenchmarkId::new("HashMap", gets), gets, |b, &gets| {
            let mut map = setup_benchmark_gets(gets);
            b.iter(|| benchmark_gets::<HashMap<i64, usize>>(&mut map, gets))
        });
        group.bench_with_input(BenchmarkId::new("BTreeMap", gets), gets, |b, &gets| {
            let mut map = setup_benchmark_gets(gets);
            b.iter(|| benchmark_gets::<BTreeMap<i64, usize>>(&mut map, gets))
        });
        group.bench_with_input(BenchmarkId::new("BSTMap", gets), gets, |b, &gets| {
            let mut map = setup_benchmark_gets(gets);
            b.iter(|| benchmark_gets::<BSTMap<i64, usize>>(&mut map, gets))
        });
    }
    group.finish();
}

pub fn bench_map_ops(c: &mut Criterion) {
    const STEPS: &[usize] = &[50, 100, 1000, 2000, 4000];

    let mut group = c.benchmark_group("map operations");
    for steps in STEPS {
        group.bench_with_input(BenchmarkId::new("HashMap", steps), steps, |b, &steps| {
            b.iter(|| benchmark_map_ops::<HashMap<i64, usize>>(steps))
        });
        group.bench_with_input(BenchmarkId::new("BTreeMap", steps), steps, |b, &steps| {
            b.iter(|| benchmark_map_ops::<BTreeMap<i64, usize>>(steps))
        });
        group.bench_with_input(BenchmarkId::new("BSTMap", steps), steps, |b, &steps| {
            b.iter(|| benchmark_map_ops::<BSTMap<i64, usize>>(steps))
        });
    }
    group.finish();
}

criterion_group!(benches,
    bench_inserts,
    bench_gets,
    bench_map_ops,
);

criterion_main!(benches);
