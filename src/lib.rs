//! iter-cools - some iterators for fun 
use std::borrow::Borrow;
use std::iter::{once,Chain,Take,Once};

use std::io;
use std::error::Error;
use std::fmt;

/// Creates an iterator from the arguments.
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

/// An iterator that splits sequence into chunks.
/// Chunck size is specified by the iterator `n`.
/// This struct is created by the [`chunks_iter()`] method on [`ChunksIteratorTrait`].
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
    /// It creates an iterator that splits sequence into chunks.
    ///
    /// ```
    /// use iter_cools::*;    
    /// 
    /// let x = (0..20u8).collect::<Vec<u8>>();
    ///
    /// let y = x.iter().chunks_iter([1,2,3].iter().cycle(),|a| a.cloned().collect::<Vec<u8>>()).collect::<Vec<_>>();
    ///
    /// let z = vec![   vec![0],    vec![1,2],      vec![3,4,5], 
    ///                 vec![6],    vec![7,8],      vec![9,10,11],
    ///                 vec![12],   vec![13,14],    vec![15,16,17],
    ///                 vec![18],   vec![19]
    ///             ];
    ///
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

#[test]
fn test_chunks(){
    fn sss<I:Iterator<Item=u8>>(i:I) -> u8{
        i.sum()
    }
    let x = (0..20u8).chunks_iter(std::iter::repeat(2),|x| -> u8 {x.sum()} ).collect::<Vec<_>>();
    assert_eq!(x, vec![]);
}

/// An iterator that maps the values of `iter` with `f`.
/// This struct is created by the [`map_ok()`] method on [`MapOkTrait`].
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
    /// Takes a closure and creates an iterator which calls that closure on each `Ok(_)` element.
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


/// An iterator that filters the elements of iter with predicate.
/// This struct is created by the [`filter_ok()`]  method on [`FilterOkTrait`].
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
    /// Creates an iterator which uses a closure to determine if an element should be yielded.
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

/// An iterator that combines two iterative sequences.
/// This struct is created by the [`punctuate()`] method on [`PunctuateTrait`].
/// [`punctuate()`]: trait.PunctuateTrait.html#method.join
/// [`PunctuateTrait`]: trait.PunctuateTrait.html
#[derive(Clone)]
pub struct PunctuateIterator<I1,I2,T1,T2> where I1:Iterator<Item=T1>, I2:Iterator<Item=T2>, T2:Into<T1>{
    it1:I1,
    it2:I2,
    idx:Option<bool>,
    nxt:Option<T1>,
    ini:bool
}

impl<I1,I2,T1,T2> Iterator for PunctuateIterator<I1,I2,T1,T2> 
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

pub trait PunctuateTrait<I, T1, T2>
where 
    Self: Sized+Iterator<Item=T1>, 
    I: IntoIterator<Item=T2>, 
    T2:Into<T1> 
{
    /// Creates iterator that combines two iterative sequences.
    ///
    /// ```
    /// use iter_cools::*;    
    ///     
    /// let v: Vec<u32> = vec![1,2,3,4,5,6];
    /// let d: Vec<u32> = vec![11,12,13,14,15,16,17,18];
    ///
    /// let s = v.iter().map(|x| x.to_string())
    ///                 .punctuate(::std::iter::repeat("+").take(2))
    ///                 .collect::<String>();
    ///
    /// assert_eq!("1+2+3", s);
    ///
    /// let s = v.into_iter().punctuate(d).collect::<Vec<u32>>();
    /// assert_eq!(vec![1, 11, 2, 12, 3, 13, 4, 14, 5, 15, 6], s);    
    /// ```    
    fn punctuate(self, i:I) -> PunctuateIterator<Self,I::IntoIter,T1,T2>{
        PunctuateIterator{it1:self, it2:i.into_iter(), idx:Some(false), ini:false, nxt:None}
    }
}

impl<I, T1, T2, X> PunctuateTrait<I, T1, T2> for X 
where 
    X: Sized + Iterator<Item=T1>, 
    I: IntoIterator<Item=T2>, 
    T2:Into<T1>
{}

/// An iterator that yields `None` forever after the underlying iterator yields `Some(Err(_))` once.
/// This struct is created by the [`fuse_err()`] on [`FuseErrTrait`].
/// [`fuse_err()`]: trait.FuseErrTrait.html#method.fuse_err
/// [`FuseErrTrait`]:trait.FuseErrTrait.html
#[derive(Clone)]
pub struct FuseErrIterator<I>(Option<I>);

impl<I,A,E> Iterator for FuseErrIterator<I> 
where I:Iterator<Item=Result<A,E>> {
    type Item = Result<A,E>;

    #[inline]
    fn next(&mut self) -> Option<Result<A,E>> {
        let res = self.0.as_mut().and_then(|x| x.next());
        if let Some(Err(_)) = res { self.0 = None };
        res
    }
}

pub trait FuseErrTrait{
    /// Creates an iterator which ends after the first `Some(Err(_))`.
    ///
    /// ```
    /// use iter_cools::*;    
    ///      
    /// let v = vec![Ok(1), Ok(2), Err("ups"), Ok(4)];
    /// let iter = v.into_iter().fuse_err();    
    /// assert_eq!(Some(Err("ups")), iter.last());
    /// ```       
    fn fuse_err<A,E>(self) -> FuseErrIterator<Self> 
    where Self: Sized + Iterator<Item=Result<A,E>> {
        FuseErrIterator(Some(self))
    }
}

impl<I,T,E> FuseErrTrait for I 
where I:Sized+Iterator<Item=Result<T,E>> {}


#[derive(Debug,Copy,Clone)]
pub enum RWError<R,W>{
    Reader(R),
    Writer(W)
}

impl<R,W> fmt::Display for RWError<R,W> 
where R: fmt::Display, W: fmt::Display
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self{
            &RWError::Reader(ref e) => write!(f, "RWError::Reader {}", e),
            &RWError::Writer(ref e) => write!(f, "RWError::Writer {}", e),
        }
    }
}

impl<R,W> Error for RWError<R,W> 
where R: Error, W: Error
{
    fn description(&self) -> &str {
        match self{
            &RWError::Reader(ref e) => e.description(),
            &RWError::Writer(ref e) => e.description(),
        }
    }

    fn cause(&self) -> Option<&Error> {
        match self{
            &RWError::Reader(ref e) => e.cause(),
            &RWError::Writer(ref e) => e.cause(),
        }
    }    
}

pub trait WriteIterBytes {
    /// Attempts to write an entire iterator to the writer. 
    /// 
    /// ```
    /// use iter_cools::*;    
    ///        
    /// let mut dest = vec![];
    /// (0..10).into_iter().write_to(&mut dest).unwrap();
    /// assert_eq!(dest, vec![0,1,2,3,4,5,6,7,8,9]); 
    /// ```     
     fn write_to<W:io::Write>(self, &mut W) -> Result<u64, RWError<(), io::Error>>;
}

pub trait WriteIterResults<E> {
    /// Attempts to write an entire iterator to the writer.
    /// 
    /// ```
    /// use iter_cools::*;    
    ///        
    /// let mut dest = vec![];
    /// (0..10).into_iter().map(|b| Ok::<u8,()>(b)).write_to(&mut dest).unwrap();
    /// assert_eq!(dest, vec![0,1,2,3,4,5,6,7,8,9]); 
    /// ```    
     fn write_to<W:io::Write>(self, &mut W) -> Result<u64, RWError<E, io::Error>>;
}

impl<T> WriteIterBytes for T
where T: Iterator<Item=u8>
{
    fn write_to<W:io::Write>(self, w: &mut W) -> Result<u64, RWError<(), io::Error>>{
        let mut cnt: u64 = 0;
        for b in self {
            w.write_all(&[b]).map_err(|e| RWError::Writer(e))?;
            cnt+=1;
        }
        Ok(cnt)
    }
}

impl<T,E> WriteIterResults<E> for T
where T: Iterator<Item=Result<u8,E>>
{
    fn write_to<W:io::Write>(self, mut w: &mut W) -> Result<u64, RWError<E, io::Error>>{
        let mut cnt: u64 = 0;
        for b in self {
            w.write_all(&[b.map_err(|e| RWError::Reader(e))?]).map_err(|e| RWError::Writer(e))?;
            cnt+=1;
        }
        Ok(cnt)
    }
}