# Route-finite posetと行列環
## モチベーション
行列環 <img src="https://latex.codecogs.com/gif.latex?\inline&space;\mathrm{M}_n(R)" /> について、その部分環として次のようなものを考えられる。
- <img src="https://latex.codecogs.com/gif.latex?\inline&space;\mathrm{M}_n(R)" />
- 対角行列のなす部分環
- 上三角行列のなす部分環
- 下三角行列のなす部分環

いずれの場合においても、これらが行列の積で閉じていることは、組み合わせ論的な議論により示すことができる。
すなわち、関数 <img src="https://latex.codecogs.com/gif.latex?\inline&space;f\colon&space;n\times&space;n\to&space;2" /> であって、
<img src="https://latex.codecogs.com/gif.latex?\inline&space;f(i,j)=0" /> ならば任意の <img src="https://latex.codecogs.com/gif.latex?\inline&space;k" /> 
に対して <img src="https://latex.codecogs.com/gif.latex?\inline&space;f(i,k)f(k,j)=0" /> であるようなものについて、
<img src="https://latex.codecogs.com/gif.latex?\inline&space;\mathrm{M}_n(R)" /> の部分環を対応させることができる。

このような <img src="https://latex.codecogs.com/gif.latex?\inline&space;f" /> はさらに、<img src="https://latex.codecogs.com/gif.latex?\inline&space;n" /> 個の対象を持つsetoidの部分圏として言い換えることができる。このとき、より一般のposetについて行列環を対応させる手続きを考えたくなる。

## Route-finite poset
半順序 <img src="https://latex.codecogs.com/gif.latex?\inline&space;P" /> がroute-finiteであるとは、以下の条件を充たすことをいう。
- 任意の <img src="https://latex.codecogs.com/gif.latex?\inline&space;i,j\in&space;P" /> に対して <img src="https://latex.codecogs.com/gif.latex?\inline&space;i\leq&space;k" /> かつ <img src="https://latex.codecogs.com/gif.latex?\inline&space;k\leq&space;j" /> なる 
<img src="https://latex.codecogs.com/gif.latex?\inline&space;k" /> は有限個

このときroute-finiteな半順序 <img src="https://latex.codecogs.com/gif.latex?\inline&space;P" /> に対してそれに伴う行列環 <img src="https://latex.codecogs.com/gif.latex?\inline&space;\mathrm{M}_P(R)" /> を考えることができる。これは以下の通り:
- <img src="https://latex.codecogs.com/gif.latex?\inline&space;i\leq&space;j" /> なる <img src="https://latex.codecogs.com/gif.latex?\inline&space;i,j\in&space;P" /> に対して 
<img src="https://latex.codecogs.com/gif.latex?\inline&space;R" /> の要素を充てる対応を元とし、そのような対応 <img src="https://latex.codecogs.com/gif.latex?\inline&space;f,g" /> について 
<img src="https://latex.codecogs.com/gif.latex?\inline&space;f*g(i,j)=\sum&space;_{i\leq&space;k\leq&space;j}f(i,k)g(k,j)" /> とおいて演算を定める

この例として、可算次元上三角行列のなす環などが考えられる。ここでposetとしては順序数 <img src="https://latex.codecogs.com/gif.latex?\inline&space;\omega" /> を取っている。
