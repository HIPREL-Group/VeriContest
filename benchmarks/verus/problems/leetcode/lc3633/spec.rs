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
    }
}

}
