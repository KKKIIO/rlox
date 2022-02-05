use std::{cell::RefCell, convert::TryInto, rc::Rc};

pub struct StrPool {
    pool: RefCell<Vec<Rc<str>>>,
}

impl StrPool {
    pub fn new() -> Self {
        Self {
            pool: RefCell::new(Vec::new()),
        }
    }

    pub fn register(&self, name: &str) -> u32 {
        let pos_res = self
            .pool
            .borrow()
            .iter()
            .position(|n| (*n).as_ref() == name);
        if let Some(i) = pos_res {
            i
        } else {
            let mut p = self.pool.borrow_mut();
            p.push(name.to_string().into_boxed_str().into());
            p.len() - 1
        }
        .try_into()
        .unwrap()
    }
    pub fn get(&self, i: u32) -> Rc<str> {
        self.pool.borrow()[i as usize].clone()
    }
    pub fn register_rc(&self, name: &str) -> Rc<str> {
        if let Some(i) = self.pool.borrow().iter().find(|n| (*n).as_ref() == name) {
            return i.clone();
        }
        let mut p = self.pool.borrow_mut();
        let name: Rc<str> = name.into();
        p.push(name.clone());
        name
    }
}
