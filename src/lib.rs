//! iter-cools - кое-какие итераторы 
use std::borrow::Borrow;
use std::iter::{once,Chain,Take,Once};

/// Создает итератор из перечисленных значений.
/// 
/// ```
/// #[macro_use]
/// extern crate iter_cools;
/// use iter_cools::*;    
/// 
/// fn main(){
///     assert_eq!(iter_it!(1,3,5,7).collect::<Vec<u8>>(), vec![1,3,5,7]);
/// }
/// ```    
#[macro_export]
macro_rules! iter_it{
    ($n:expr,$($m:expr),*) => {::std::iter::once($n)$(.chain(::std::iter::once($m)))*}
}

/// Итератор, который разбивает итерационную последовательность на порции.
/// Размер порций задается с помощью итератора `n`.
/// Создается функцией [`chunks_iter()`]  типажа [`ChunksIteratorTrait`].
/// [`chunks_iter()`]: trait.ChunksIteratorTrait.html#method.chunks_iter
/// [`ChunksIteratorTrait`]: trait.ChunksIteratorTrait.html
#[derive(Clone)]
pub struct ChunksIterator<I,F,N>{
    iter:I,
    n:N,
    f:F
}

impl<B,I,T,F,N,M> Iterator for ChunksIterator<I,F,N> 
where 
    N:Iterator<Item=M>, M:Borrow<usize>,
    I:Iterator<Item=T>,
    F:FnMut(Chain<Once<T>, Take<&mut I>>) -> B,
{
    type Item = B;

    #[inline]
    fn next(&mut self) -> Option<B> {
        match self.n.next().map(|x| *x.borrow()) {
            Some(0) => None, 
            Some(n) => self.iter.next()
                                .map(|t| 
                                    (self.f)(once(t).chain(self.iter.by_ref().take(n-1)))
                                ),
            None => None,
        }
    }
}

pub trait ChunksIteratorTrait{
    /// Создает итератор разбивающий итерационную последовательность на порции.
    ///
    /// ```
    /// use iter_cools::*;    
    /// 
    /// let x = (0..20u8).collect::<Vec<u8>>();
    /// let y = x.iter().chunks_iter([1,2,3].iter().cycle(),|a| a.cloned().collect::<Vec<u8>>()).collect::<Vec<_>>();
    /// let z = vec![vec![0],vec![1,2],vec![3,4,5],vec![6],vec![7,8],vec![9,10,11],vec![12],vec![13,14],vec![15,16,17],vec![18],vec![19]];
    /// assert_eq!(z, y);
    /// ```
    fn chunks_iter<F,B,T,N,M>(self, n:N, f:F) -> ChunksIterator<Self,F,N::IntoIter>
    where 
        N:IntoIterator<Item=M>, M:Borrow<usize>,
        Self:Iterator<Item=T> + Sized,
        F:FnMut(Chain<Once<T>, Take<&mut Self>>) -> B
    {
        ChunksIterator{iter:self, n:n.into_iter(), f:f}
    }
}

impl<I,T> ChunksIteratorTrait for I 
where 
    I:Iterator<Item=T>,
{}

/// Итератор, который заменяет элементы итерационной последовательности.
/// Создается функцией [`map_ok()`]  типажа [`MapOkTrait`].
/// [`map_ok()`]: trait.MapOkTrait.html#method.map_ok
/// [`MapOkTrait`]: trait.MapOkTrait.html
#[derive(Clone)]
pub struct MapOkIterator<I,F>{
    iter:I,
    f:F
}

impl<A,B,E,I,F> Iterator for MapOkIterator<I,F> 
where 
    F:FnMut(A) -> B, 
    I:Iterator<Item=Result<A,E>> {

    type Item = Result<B,E>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|x| x.map(&mut self.f))
    }
}

pub trait MapOkTrait{
    /// Создает итератор, который заменяет элементы итерационной последовательности.
    ///
    /// ```
    /// use iter_cools::*;    
    ///     
    /// let x = vec![Ok(1),Ok(2),Err("ups"),Ok(4)];
    /// let y = x.iter().cloned().map_ok(|x| x + 2).collect::<Result<Vec<usize>,_>>();
    /// assert_eq!(Err("ups"), y);
    ///
    /// let x:Vec<Result<usize,()>> = vec![Ok(1),Ok(2),Ok(3),Ok(4)];
    /// let y = x.iter().cloned().map_ok(|x| x + 2).collect::<Result<Vec<usize>,_>>();
    /// assert_eq!(Ok(vec![3,4,5,6]), y); 
    /// ```    
    fn map_ok<F,A,B,E>(self, func:F) -> MapOkIterator<Self, F>
    where 
        Self:Sized+Iterator<Item=Result<A,E>>, 
        F:FnMut(A) -> B 
    {
        MapOkIterator{iter:self, f:func}
    }
}

impl<I,T,E> MapOkTrait for I 
where I:Sized+Iterator<Item=Result<T,E>>{}


/// Итератор, который фильтрует элементы итерационной последовательности.
/// Создается функцией [`filter_ok()`]  типажа [`FilterOkTrait`].
/// [`filter_ok()`]: trait.FilterOkTrait.html#method.filter_ok
/// [`FilterOkTrait`]: trait.FilterOkTrait.html
#[derive(Clone)]
pub struct FilterOkIterator<I,P>{
    iter: I,
    predicate: P,
}

impl<I,P,A,E> Iterator for FilterOkIterator<I,P> 
where 
    P:FnMut(&A) -> bool, 
    I:Iterator<Item=Result<A,E>> {

    type Item = Result<A,E>;

    #[inline]
    fn next(&mut self) -> Option<Result<A,E>> {
        for x in self.iter.by_ref() {
            match x {
                Ok(xx) => if (self.predicate)(&xx) {
                    return Some(Ok(xx));
                },
                Err(_) => return Some(x)
            }
        }
        None
    }
}

pub trait FilterOkTrait{
    /// Создает итератор, который фильтрует элементы итерационной последовательности
    ///
    /// ```
    /// use iter_cools::*;    
    ///     
    /// let x = vec![Ok(1),Ok(2),Err("ups"),Ok(4)];
    /// let y = x.iter().cloned().filter_ok(|&x| x>2).collect::<Result<Vec<usize>,_>>();
    /// assert_eq!(Err("ups"), y);
    /// 
    /// let x:Vec<Result<usize,()>> = vec![Ok(1),Ok(2),Ok(3),Ok(4)];
    /// let y = x.iter().cloned().filter_ok(|&x| x>2).collect::<Result<Vec<usize>,_>>();
    /// assert_eq!(Ok(vec![3,4]), y);
    /// ```      
    fn filter_ok<P, A, E>(self, predicate: P) -> FilterOkIterator<Self, P> 
    where 
        Self: Sized + Iterator<Item=Result<A,E>>, 
        P: FnMut(&A) -> bool {
        
        FilterOkIterator{iter: self, predicate: predicate}
    }
}

impl<I,T,E> FilterOkTrait for I 
where I:Sized+Iterator<Item=Result<T,E>>{}

/// Итератор, который объединяет две итерационные последовательности.
/// Создается функцией [`join_iter()`]  типажа [`JoinTrait`].
/// [`join_iter()`]: trait.JoinTrait.html#method.join
/// [`JoinTrait`]: trait.JoinTrait.html
#[derive(Clone)]
pub struct JoinIterator<I1,I2,T1,T2> where I1:Iterator<Item=T1>, I2:Iterator<Item=T2>, T2:Into<T1>{
    it1:I1,
    it2:I2,
    idx:Option<bool>,
    nxt:Option<T1>,
    ini:bool
}

impl<I1,I2,T1,T2> Iterator for JoinIterator<I1,I2,T1,T2> 
where 
    I1: Iterator<Item=T1>, 
    I2: Iterator<Item=T2>, 
    T2: Into<T1>
{
    type Item = T1;
    fn next(&mut self) -> Option<T1> {
        if !self.ini {self.nxt = self.it1.next(); self.ini = true;}
        let res = match self.idx {
            Some(false) => {
                self.nxt.take()
            },
            Some(true) => {
                self.nxt = self.it1.next();
                if self.nxt.is_some() {
                    self.it2.next().map(|x|x.into())
                }else{None}
            },
            None => None
        };
        self.idx = if res.is_none() {None}else{self.idx.map(|x|!x)};
        res
    }
}

pub trait JoinTrait<I, T1, T2>
where 
    Self: Sized+Iterator<Item=T1>, 
    I: IntoIterator<Item=T2>, 
    T2:Into<T1> 
{
    /// Создает итератор, который объединяет две итерационные последовательности.
    ///
    /// ```
    /// use iter_cools::*;    
    ///     
    /// let v: Vec<u32> = vec![1,2,3,4,5,6];
    /// let d: Vec<u32> = vec![11,12,13,14,15,16,17,18];
    ///
    /// let s = v.iter().map(|x| x.to_string()).join_iter(::std::iter::repeat("+").take(2)).collect::<String>();
    /// assert_eq!("1+2+3", s);
    ///
    /// let s = v.into_iter().join_iter(d).collect::<Vec<u32>>();
    /// assert_eq!(vec![1, 11, 2, 12, 3, 13, 4, 14, 5, 15, 6], s);    
    /// ```    
    fn join_iter(self, i:I) -> JoinIterator<Self,I::IntoIter,T1,T2>{
        JoinIterator{it1:self, it2:i.into_iter(), idx:Some(false), ini:false, nxt:None}
    }
}

impl<I, T1, T2, X> JoinTrait<I, T1, T2> for X 
where 
    X: Sized + Iterator<Item=T1>, 
    I: IntoIterator<Item=T2>, 
    T2:Into<T1>
{}
 
