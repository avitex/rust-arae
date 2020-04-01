use arae::{CurVec, CursedExt};

fn main() {
    static VAL: &u8 = &1;

    let mut vec: CurVec<&u8> = vec![VAL].into();
    
    *vec.get_mut(vec.hptr()) = &2;

    assert_eq!(*VAL, 1);
}
