pub struct Multiset<T> {
    data: HashMap<T, usize>,
}

impl<T: Eq + Hash> Multiset<T> {
    pub fn new() -> Self {
        Self { data: HashMap::new() }
    }

    pub fn insert(&mut self, item: T) {
        *self.data.entry(item).or_insert(0) += 1;
    }

    pub fn remove(&mut self, item: T) {
        if let Some(count) = self.data.get_mut(&item) {
            if *count > 1 {
                *count -= 1;
            } else {
                self.data.remove(&item);
            }
        }
    }

    pub fn merge(&mut self, other: &Self) {
        for (item, &count) in &other.data {
            *self.data.entry(item.clone()).or_insert(0) += count;
        }
    }
}
