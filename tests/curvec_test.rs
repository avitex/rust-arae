use arae::{Bounded, CurVec, CursedExt, Sequence};

#[test]
#[should_panic]
fn test_new_empty() {
    CurVec::<u8>::new_with_default(0);
}

#[test]
#[should_panic]
fn test_from_empty_vec() {
    let _: CurVec<u8> = vec![].into();
}

#[test]
fn test_new_with_default() {
    let vec = CurVec::<u8>::new_with_default(1);
    assert_eq!(vec.as_slice(), &[0][..]);
}

#[test]
fn test_clone() {
    let vec: CurVec<_> = vec![1, 2, 3].into();
    let vec_clone = vec.clone();
    assert_eq!(vec, vec_clone);
}

#[test]
fn test_get() {
    let vec: CurVec<_> = vec![1, 2, 3].into();
    assert_eq!(vec.len(), 3);

    let cursor = vec.hptr();

    assert_eq!(*vec.get(cursor), 1);

    let cursor = vec.next(cursor).unwrap();
    assert_eq!(*vec.get(cursor), 2);

    let cursor = vec.next(cursor).unwrap();
    assert_eq!(*vec.get(cursor), 3);

    assert_eq!(vec.next(cursor), None);
}

#[test]
fn test_get_mut() {
    let mut vec: CurVec<_> = vec![1, 2, 3].into();
    *vec.get_mut(vec.hptr()) = 2;
    assert_eq!(vec, vec![2, 2, 3].into());
}

#[test]
fn test_at_invalid() {
    let vec: CurVec<_> = vec![1].into();
    assert_eq!(vec.at(1), None);
}

#[test]
fn test_iter() {
    let vec: CurVec<_> = vec![1, 2].into();
    let mut vec_iter = vec.iter();

    let (_, cursor) = vec_iter.next().unwrap();
    assert_eq!(*vec.get(cursor), 1);
    assert_eq!(vec.offset(cursor), 0);

    let (_, cursor) = vec_iter.next().unwrap();
    assert_eq!(*vec.get(cursor), 2);
    assert_eq!(vec.offset(cursor), 1);
    assert!(vec.is_tail(cursor));

    assert_eq!(vec_iter.next(), None);
}

#[test]
fn test_iter_single_elem() {
    let vec: CurVec<_> = vec![1].into();
    let mut vec_iter = vec.iter();

    let (_, cursor) = vec_iter.next().unwrap();
    assert_eq!(*vec.get(cursor), 1);
    assert!(vec.is_head(cursor));
    assert!(vec.is_tail(cursor));

    assert_eq!(vec_iter.next(), None);
}

#[test]
fn test_iter_at() {
    let vec: CurVec<_> = vec![1, 2].into();
    let mut vec_iter = vec.iter_at(vec.at(1).unwrap());

    let (_, cursor) = vec_iter.next().unwrap();
    assert_eq!(*vec.get(cursor), 2);
    assert_eq!(vec.offset(cursor), 1);
    assert!(vec.is_tail(cursor));

    assert_eq!(vec_iter.next(), None);
}

#[test]
fn test_wrapping_iter() {
    let vec: CurVec<_> = vec![1, 2].into();
    let mut vec_iter = vec.wrapping_iter();

    let (_, cursor) = vec_iter.next().unwrap();
    assert_eq!(*vec.get(cursor), 1);
    assert_eq!(vec.offset(cursor), 0);

    let (_, cursor) = vec_iter.next().unwrap();
    assert_eq!(*vec.get(cursor), 2);
    assert_eq!(vec.offset(cursor), 1);
    assert!(vec.is_tail(cursor));

    let (_, cursor) = vec_iter.next().unwrap();
    assert_eq!(vec.offset(cursor), 0);
}

#[test]
fn test_wrapping_iter_at() {
    let vec: CurVec<_> = vec![1, 2].into();
    let mut vec_iter = vec.wrapping_iter_at(vec.at(1).unwrap());

    let (_, cursor) = vec_iter.next().unwrap();
    assert_eq!(*vec.get(cursor), 2);
    assert_eq!(vec.offset(cursor), 1);
    assert!(vec.is_tail(cursor));

    let (_, cursor) = vec_iter.next().unwrap();
    assert_eq!(*vec.get(cursor), 1);
    assert_eq!(vec.offset(cursor), 0);
}
