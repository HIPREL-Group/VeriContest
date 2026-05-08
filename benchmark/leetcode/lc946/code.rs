impl Solution {
    fn reduce_stack_exec(stack: &mut Vec<i32>, popped: &Vec<i32>, j: usize) -> usize {
        if stack.len() > 0 && j < popped.len() && stack[stack.len() - 1] == popped[j] {
            stack.pop();
            Self::reduce_stack_exec(stack, popped, j + 1)
        } else {
            j
        }
    }

    pub fn validate_stack_sequences(pushed: Vec<i32>, popped: Vec<i32>) -> bool {
        let n = pushed.len();
        let mut stack: Vec<i32> = Vec::new();
        let mut i = 0usize;
        let mut j = 0usize;
        while i < n {
            stack.push(pushed[i]);
            i = i + 1;
            j = Self::reduce_stack_exec(&mut stack, &popped, j);
        }
        stack.len() == 0
    }
}
