use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn pair_time(
        land_start_time: Seq<i32>,
        land_duration: Seq<i32>,
        water_start_time: Seq<i32>,
        water_duration: Seq<i32>,
        i: int,
        j: int,
    ) -> int
        recommends
            0 <= i < land_start_time.len(),
            0 <= j < water_start_time.len(),
            land_start_time.len() == land_duration.len(),
            water_start_time.len() == water_duration.len(),
    {
        let land_finish = land_start_time[i] as int + land_duration[i] as int;
        let land_then_water = if water_start_time[j] as int > land_finish {
            water_start_time[j] as int + water_duration[j] as int
        } else {
            land_finish + water_duration[j] as int
        };
        let water_finish = water_start_time[j] as int + water_duration[j] as int;
        let water_then_land = if land_start_time[i] as int > water_finish {
            land_start_time[i] as int + land_duration[i] as int
        } else {
            water_finish + land_duration[i] as int
        };
        if land_then_water <= water_then_land {
            land_then_water
        } else {
            water_then_land
        }
    }

    fn pair_time_exec(
        land_start_time: &Vec<i32>,
        land_duration: &Vec<i32>,
        water_start_time: &Vec<i32>,
        water_duration: &Vec<i32>,
        i: usize,
        j: usize,
    ) -> (res: i32)
        requires
            land_start_time.len() == land_duration.len(),
            water_start_time.len() == water_duration.len(),
            0 <= i < land_start_time.len(),
            0 <= j < water_start_time.len(),
            forall|k: int| 0 <= k < land_start_time.len() ==> 1 <= #[trigger] land_start_time[k] <= 1000,
            forall|k: int| 0 <= k < land_duration.len() ==> 1 <= #[trigger] land_duration[k] <= 1000,
            forall|k: int| 0 <= k < water_start_time.len() ==> 1 <= #[trigger] water_start_time[k] <= 1000,
            forall|k: int| 0 <= k < water_duration.len() ==> 1 <= #[trigger] water_duration[k] <= 1000,
        ensures
            res as int
                == Self::pair_time(
                    land_start_time@,
                    land_duration@,
                    water_start_time@,
                    water_duration@,
                    i as int,
                    j as int,
                ),
    {
        let land_finish = land_start_time[i] + land_duration[i];
        let land_then_water = if water_start_time[j] > land_finish {
            water_start_time[j] + water_duration[j]
        } else {
            land_finish + water_duration[j]
        };
        let water_finish = water_start_time[j] + water_duration[j];
        let water_then_land = if land_start_time[i] > water_finish {
            land_start_time[i] + land_duration[i]
        } else {
            water_finish + land_duration[i]
        };
        if land_then_water <= water_then_land {
            land_then_water
        } else {
            water_then_land
        }
    }

    pub fn earliest_finish_time(
        land_start_time: Vec<i32>,
        land_duration: Vec<i32>,
        water_start_time: Vec<i32>,
        water_duration: Vec<i32>,
    ) -> (result: i32)
        requires
            1 <= land_start_time.len() <= 100,
            1 <= water_start_time.len() <= 100,
            land_start_time.len() == land_duration.len(),
            water_start_time.len() == water_duration.len(),
            forall|k: int| 0 <= k < land_start_time.len() ==> 1 <= #[trigger] land_start_time[k] <= 1000,
            forall|k: int| 0 <= k < land_duration.len() ==> 1 <= #[trigger] land_duration[k] <= 1000,
            forall|k: int| 0 <= k < water_start_time.len() ==> 1 <= #[trigger] water_start_time[k] <= 1000,
            forall|k: int| 0 <= k < water_duration.len() ==> 1 <= #[trigger] water_duration[k] <= 1000,
        ensures
            exists|i: int, j: int|
                0 <= i < land_start_time.len()
                    && 0 <= j < water_start_time.len()
                    && result as int
                        == Self::pair_time(
                            land_start_time@,
                            land_duration@,
                            water_start_time@,
                            water_duration@,
                            i,
                            j,
                        ),
            forall|i: int, j: int|
                0 <= i < land_start_time.len() && 0 <= j < water_start_time.len() ==> result as int
                    <= Self::pair_time(
                        land_start_time@,
                        land_duration@,
                        water_start_time@,
                        water_duration@,
                        i,
                        j,
                    ),
    {
        let n = land_start_time.len();
        let m = water_start_time.len();
        let mut best = Self::pair_time_exec(
            &land_start_time,
            &land_duration,
            &water_start_time,
            &water_duration,
            0,
            0,
        );
        let ghost mut best_i: int = 0;
        let ghost mut best_j: int = 0;

        let mut i: usize = 0;
        while i < n
            invariant
                n == land_start_time.len(),
                m == water_start_time.len(),
                1 <= n <= 100,
                1 <= m <= 100,
                land_start_time.len() == land_duration.len(),
                water_start_time.len() == water_duration.len(),
                forall|k: int| 0 <= k < land_start_time.len() ==> 1 <= #[trigger] land_start_time[k] <= 1000,
                forall|k: int| 0 <= k < land_duration.len() ==> 1 <= #[trigger] land_duration[k] <= 1000,
                forall|k: int| 0 <= k < water_start_time.len() ==> 1 <= #[trigger] water_start_time[k] <= 1000,
                forall|k: int| 0 <= k < water_duration.len() ==> 1 <= #[trigger] water_duration[k] <= 1000,
                0 <= i <= n,
                0 <= best_i < n as int,
                0 <= best_j < m as int,
                best as int
                    == Self::pair_time(
                        land_start_time@,
                        land_duration@,
                        water_start_time@,
                        water_duration@,
                        best_i,
                        best_j,
                    ),
                forall|p: int, q: int|
                    0 <= p < i as int && 0 <= q < m as int ==> best as int
                        <= Self::pair_time(
                            land_start_time@,
                            land_duration@,
                            water_start_time@,
                            water_duration@,
                            p,
                            q,
                        ),
            decreases n - i,
        {
            let mut j: usize = 0;
            while j < m
                invariant
                    n == land_start_time.len(),
                    m == water_start_time.len(),
                    1 <= n <= 100,
                    1 <= m <= 100,
                    land_start_time.len() == land_duration.len(),
                    water_start_time.len() == water_duration.len(),
                    forall|k: int| 0 <= k < land_start_time.len() ==> 1 <= #[trigger] land_start_time[k] <= 1000,
                    forall|k: int| 0 <= k < land_duration.len() ==> 1 <= #[trigger] land_duration[k] <= 1000,
                    forall|k: int| 0 <= k < water_start_time.len() ==> 1 <= #[trigger] water_start_time[k] <= 1000,
                    forall|k: int| 0 <= k < water_duration.len() ==> 1 <= #[trigger] water_duration[k] <= 1000,
                    0 <= i < n,
                    0 <= j <= m,
                    0 <= best_i < n as int,
                    0 <= best_j < m as int,
                    best as int
                        == Self::pair_time(
                            land_start_time@,
                            land_duration@,
                            water_start_time@,
                            water_duration@,
                            best_i,
                            best_j,
                        ),
                    forall|p: int, q: int|
                        ((0 <= p < i as int && 0 <= q < m as int)
                            || (p == i as int && 0 <= q < j as int)) ==> best as int
                            <= Self::pair_time(
                                land_start_time@,
                                land_duration@,
                                water_start_time@,
                                water_duration@,
                                p,
                                q,
                            ),
                decreases m - j,
            {
                let ghost old_best = best as int;
                let candidate = Self::pair_time_exec(
                    &land_start_time,
                    &land_duration,
                    &water_start_time,
                    &water_duration,
                    i,
                    j,
                );

                if candidate < best {
                    best = candidate;
                    proof {
                        best_i = i as int;
                        best_j = j as int;
                    }
                }

                proof {
                    assert(candidate as int
                        == Self::pair_time(
                            land_start_time@,
                            land_duration@,
                            water_start_time@,
                            water_duration@,
                            i as int,
                            j as int,
                        ));

                    if candidate < old_best as i32 {
                        assert(best as int == candidate as int);
                    } else {
                        assert(best as int == old_best);
                    }
                    assert(best as int <= old_best);
                    assert(best as int <= candidate as int);

                    assert forall|p: int, q: int|
                        ((0 <= p < i as int && 0 <= q < m as int)
                            || (p == i as int && 0 <= q < j as int)) implies best as int
                            <= Self::pair_time(
                                land_start_time@,
                                land_duration@,
                                water_start_time@,
                                water_duration@,
                                p,
                                q,
                            ) by {
                        assert(old_best <= Self::pair_time(
                            land_start_time@,
                            land_duration@,
                            water_start_time@,
                            water_duration@,
                            p,
                            q,
                        ));
                        assert(best as int <= old_best);
                    };
                }

                j += 1;
            }

            proof {
                assert(j == m);
                assert forall|p: int, q: int|
                    0 <= p < (i + 1) as int && 0 <= q < m as int implies best as int
                        <= Self::pair_time(
                            land_start_time@,
                            land_duration@,
                            water_start_time@,
                            water_duration@,
                            p,
                            q,
                        ) by {
                    if p < i as int {
                        assert((0 <= p < i as int && 0 <= q < m as int)
                            || (p == i as int && 0 <= q < j as int));
                    } else {
                        assert(p == i as int);
                        assert(0 <= q < j as int);
                        assert((0 <= p < i as int && 0 <= q < m as int)
                            || (p == i as int && 0 <= q < j as int));
                    }
                };
            }

            i += 1;
        }

        best
    }
}

}
