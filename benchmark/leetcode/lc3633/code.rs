impl Solution {
    fn pair_time_exec(
        land_start_time: &Vec<i32>,
        land_duration: &Vec<i32>,
        water_start_time: &Vec<i32>,
        water_duration: &Vec<i32>,
        i: usize,
        j: usize,
    ) -> i32 {
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
    ) -> i32 {
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

        let mut i: usize = 0;
        while i < n {
            let mut j: usize = 0;
            while j < m {
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
                }
                j += 1;
            }
            i += 1;
        }

        best
    }
}
