impl Solution {
    pub fn filter_restaurants(
        restaurants: Vec<Vec<i32>>,
        vegan_friendly: i32,
        max_price: i32,
        max_distance: i32,
    ) -> Vec<i32> {
        let n = restaurants.len();
        let mut indices: Vec<usize> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            if (vegan_friendly == 0 || restaurants[i][2] == 1)
                && restaurants[i][3] <= max_price
                && restaurants[i][4] <= max_distance
            {
                indices.push(i);
            }
            i += 1;
        }
        let m = indices.len();
        let mut j: usize = 0;
        while j < m {
            let mut best: usize = j;
            let mut k: usize = j + 1;
            while k < m {
                let ik = indices[k];
                let ib = indices[best];
                if restaurants[ik][1] > restaurants[ib][1]
                    || (restaurants[ik][1] == restaurants[ib][1]
                        && restaurants[ik][0] > restaurants[ib][0])
                {
                    best = k;
                }
                k += 1;
            }
            let val_j = indices[j];
            let val_best = indices[best];
            indices[j] = val_best;
            indices[best] = val_j;
            j += 1;
        }
        let mut result: Vec<i32> = Vec::new();
        let mut l: usize = 0;
        while l < m {
            result.push(restaurants[indices[l]][0]);
            l += 1;
        }
        result
    }
}
