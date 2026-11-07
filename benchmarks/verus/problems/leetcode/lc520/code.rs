impl Solution {
    pub fn detect_capital_use(word: String) -> bool
    {
        let len = word.as_str().unicode_len();
        let mut all_upper = true;
        let mut i: usize = 0;

        while i < len && all_upper
        {
            let c = word.as_str().get_char(i);
            if !(c >= 'A' && c <= 'Z') {
                all_upper = false;
            }
            i += 1;
        }
        
        if all_upper {
            return true;
        }
        
        let mut all_lower = true;
        i = 0;
        while i < len && all_lower
        {
            let c = word.as_str().get_char(i);
            if !(c >= 'a' && c <= 'z') {
                all_lower = false;
            }
            i += 1;
        }
        
        if all_lower {
            return true;
        }
        
        let first = word.as_str().get_char(0);
        if !(first >= 'A' && first <= 'Z') {
            return false;
        }
                
        i = 1;
        let mut rest_lower = true;
        while i < len && rest_lower
        {
            let c = word.as_str().get_char(i);
            if !(c >= 'a' && c <= 'z') {
                rest_lower = false;
            }
            i += 1;
        }
        
        rest_lower
    }
}
