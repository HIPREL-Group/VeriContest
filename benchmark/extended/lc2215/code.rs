impl Solution {
    pub fn find_difference(nums1: Vec<i32>, nums2: Vec<i32>) -> Vec<Vec<i32>> {
        let mut diff1 = Vec::new();
        let mut i = 0;

        while i < nums1.len()
        {
            let candidate = nums1[i];

            let mut j = 0;
            let mut found_in_nums2 = false;

            while j < nums2.len()
            {
                if nums2[j] == candidate {
                    found_in_nums2 = true;
                }
                j = j + 1;
            }

            if !found_in_nums2 {
                let mut k = 0;
                let mut already_in_diff1 = false;

                while k < diff1.len()
                {
                    if diff1[k] == candidate {
                        already_in_diff1 = true;
                    }
                    k = k + 1;
                }

                if !already_in_diff1 {
                    diff1.push(candidate);
                }
            }

            i = i + 1;
        }

        let mut diff2 = Vec::new();
        let mut i2 = 0;

        while i2 < nums2.len()
        {
            let candidate = nums2[i2];

            let mut j = 0;
            let mut found_in_nums1 = false;

            while j < nums1.len()
            {
                if nums1[j] == candidate {
                    found_in_nums1 = true;
                }
                j = j + 1;
            }

            if !found_in_nums1 {
                let mut k = 0;
                let mut already_in_diff2 = false;

                while k < diff2.len()
                {
                    if diff2[k] == candidate {
                        already_in_diff2 = true;
                    }
                    k = k + 1;
                }

                if !already_in_diff2 {
                    diff2.push(candidate);
                }
            }

            i2 = i2 + 1;
        }

        let mut result = Vec::new();
        result.push(diff1);
        result.push(diff2);

        result
    }
}