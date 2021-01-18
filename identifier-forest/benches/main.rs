use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use identifier_forest::quad::{
    GSPOGreedy, GSPOLazy, Order, QuadForest, QuadForestProfile, RuntimeFat, RuntimeSlim,
};

fn load_lazy(c: &mut Criterion) {
    let mut group = c.benchmark_group("Load lazy");
    use Order::*;
    group.bench_function("Runtime fat", |b| {
        b.iter(|| {
            load_into(&mut QuadForest::<RuntimeFat>::new_rt(
                &[GSPO],
                &[SPOG, PGSO, OPSG, SOGP, GOPS],
            ))
        })
    });
    group.bench_function("Runtime slim", |b| {
        b.iter(|| {
            load_into(&mut QuadForest::<RuntimeSlim>::new_rt(
                &[GSPO],
                &[SPOG, PGSO, OPSG, SOGP, GOPS],
            ))
        })
    });
    group.bench_function("Compile time", |b| {
        b.iter(|| load_into(&mut QuadForest::<GSPOLazy>::new()))
    });
    group.finish();
}

fn load_greedy(c: &mut Criterion) {
    let mut group = c.benchmark_group("Load greedy");
    use Order::*;
    group.bench_function("Runtime fat", |b| {
        b.iter(|| {
            load_into(&mut QuadForest::<RuntimeFat>::new_rt(
                &[GSPO, SPOG, PGSO, OPSG, SOGP, GOPS],
                &[],
            ))
        })
    });
    group.bench_function("Runtime slim", |b| {
        b.iter(|| {
            load_into(&mut QuadForest::<RuntimeSlim>::new_rt(
                &[GSPO, SPOG, PGSO, OPSG, SOGP, GOPS],
                &[],
            ))
        })
    });
    group.bench_function("Compile time", |b| {
        b.iter(|| load_into(&mut QuadForest::<GSPOGreedy>::new()))
    });
    group.finish();
}

fn search_lazy(c: &mut Criterion) {
    let mut group = c.benchmark_group("Search lazy");
    use Order::*;
    group.bench_function("Runtime fat", |b| {
        b.iter_batched(
            || {
                let mut forest =
                    QuadForest::<RuntimeFat>::new_rt(&[GSPO], &[SPOG, PGSO, OPSG, SOGP, GOPS]);
                load_into(&mut forest);
                forest
            },
            |forest| {
                forest
                    .iter_matching([None, Some(42), None, None])
                    .collect::<Vec<_>>()
            },
            BatchSize::LargeInput,
        )
    });
    group.bench_function("Runtime slim", |b| {
        b.iter_batched(
            || {
                let mut forest =
                    QuadForest::<RuntimeSlim>::new_rt(&[GSPO], &[SPOG, PGSO, OPSG, SOGP, GOPS]);
                load_into(&mut forest);
                forest
            },
            |forest| {
                forest
                    .iter_matching([None, Some(42), None, None])
                    .collect::<Vec<_>>()
            },
            BatchSize::LargeInput,
        )
    });
    group.bench_function("Compile time", |b| {
        b.iter_batched(
            || {
                let mut forest = QuadForest::<GSPOLazy>::new();
                load_into(&mut forest);
                forest
            },
            |forest| {
                forest
                    .iter_matching([None, Some(42), None, None])
                    .collect::<Vec<_>>()
            },
            BatchSize::LargeInput,
        )
    });
    group.finish();
}

fn search_prebuilt(c: &mut Criterion) {
    let mut group = c.benchmark_group("Search prebuilt");
    use Order::*;

    let mut forest = QuadForest::<RuntimeFat>::new_rt(&[GSPO, SPOG, PGSO, OPSG, SOGP, GOPS], &[]);
    load_into(&mut forest);
    group.bench_with_input("Runtime fat", &forest, |b, forest| {
        b.iter(|| {
            forest
                .iter_matching([None, Some(42), None, None])
                .collect::<Vec<_>>()
        })
    });

    let mut forest = QuadForest::<RuntimeSlim>::new_rt(&[GSPO, SPOG, PGSO, OPSG, SOGP, GOPS], &[]);
    load_into(&mut forest);
    group.bench_with_input("Runtime slim", &forest, |b, forest| {
        b.iter(|| {
            forest
                .iter_matching([None, Some(42), None, None])
                .collect::<Vec<_>>()
        })
    });

    let mut forest = QuadForest::<GSPOGreedy>::new();
    load_into(&mut forest);
    group.bench_with_input("Compile time", &forest, |b, forest| {
        b.iter(|| {
            forest
                .iter_matching([None, Some(42), None, None])
                .collect::<Vec<_>>()
        })
    });

    group.finish();
}

fn load_into<P: QuadForestProfile<Identifier = usize>>(forest: &mut QuadForest<P>) {
    const MAX: usize = 5000;
    for s in 1..=MAX {
        for p in 1..=MAX {
            if s * p < MAX {
                forest.insert([s, p, s * p, p % 2]);
            }
        }
    }
}

criterion_group!(benches, search_prebuilt, search_lazy, load_greedy, load_lazy);
//criterion_group!(benches, load_lazy); // strange: load_lazy is much faster when it is the only benchmark...
criterion_main!(benches);
