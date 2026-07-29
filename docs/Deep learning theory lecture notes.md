# Deep learning theory lecture notes

Matus Telgarsky mjt@illinois.edu

2021-10-27 v0.0-e7150f2d (alpha)

###### Contents

* 1 Approximation: preface
	* 1.1 Omitted topics
* 2 Classical approximations and "universal approximation"
	* 2.1 Elementary folklore constructions
	* 2.2 Universal approximation with a single hidden layer
* 3 Infinite-width Fourier representations and the Barron norm
	* 3.1 Infinite-width univariate approximations
	* 3.2 Barron's construction for infinite-width multivariate approximation
	* 3.3 Sampling from infinite width networks
* 4 Approximation near initialization and the Neural Tangent Kernel
	* 4.1 Basic setup: Taylor expansion of shallow networks
	* 4.2 Networks near initialization are almost linear
	* 4.3 Properties of the kernel at initialization
* 5 Benefits of depth
	* 5.1 The humble \(\Delta\) mapping.
	* 5.2 Separating shallow and deep networks
	* 5.3 Approximating \(x^{2}\)
	* 5.4 Sobolev balls
* 6 Optimization: preface
	* 6.1 Omitted topics
* 7 Semi-classical convex optimization
	* 7.1 Smooth objectives in ML
		* 7.1.1 Convergence to stationary points
		* 7.1.2 Convergence rate for smooth & convex
	* 7.2 Strong convexity
		* 7.2.1 Rates when strongly convex and smooth

## Preface

**Philosophy of these notes.** Two key ideas determined what has been included so far.

1. I aim to provide simplified proofs over what appears in the literature, ideally reducing difficult things to something that fits in a single lecture.
2. I have primarily focused on a classical perspective of achieving a low test error for binary classification with IID data via standard (typically ReLU) feedforward networks.

**Organization.** Following the second point above, the classical view decomposes the test error into three parts.

1. **Approximation (starts in section 1):** given a classification problem, there exists a deep network which achieves low error _over the distribution_.
2. **Optimization (starts in section 6):** given a finite training set for a classification problem, there exist algorithms to find predictors with low training error _and low complexity_.
3. **Generalization (starts in section 11):** the gap between training and testing error is small for low complexity networks.

**Remark 0.1**: _(weaknesses of this "classical" approach)_

* Recent influential work suggests that the classical perspective is hopelessly loose, and has poor explanatory power (Neyshabur, Tomioka, and Srebro 2014; Zhang et al. 2017). Follow-ups highlight this looseness and its lack of correlation with good test error performance (Dziugaite and Roy 2017), and even suggest the basic approach is flawed (Nagarajan and Kolter 2019); please see section 11.1 for further discussion and references.
* The reasons for keeping with this approach here are as follows: 1. It appears that all of these negative results consider the consequences of _worst-case_ behavior in one of these three terms on the other two. Here instead we study how they inter-connect in a favorable way. A common them is how they all work together with _low complexity models_ on reasonable data. 2. Even if the preceding point is overly optimistic at times, this decomposition still gives us a way to organize and categorize much of what is known in the field, and secondly these ideas will always be useful at least as tools in a broader picture.

**Formatting.**

* These notes use pandoc markdown with various extensions. A current html version is always at [https://mjt.cs.illinois.edu/dlt/](https://mjt.cs.illinois.edu/dlt/), and a current pdf version is always at [https://mjt.cs.illinois.edu/dlt/index.pdf](https://mjt.cs.illinois.edu/dlt/index.pdf).
* Owing to my unfamiliarity with pandoc, there are still various formatting bugs.
* [ mjt(r): Various todo notes are marked throughout the text like this.]

**Feedback.** I'm very eager to hear any and all feedback!

**How to cite.** Please consider using a format which makes the version clear:

@misc{mjt_dlt,  author = {Matus Telgarsky},  title = {Deep learning theory lecture notes},  howpublished = {url{[https://mjt.cs.illinois.edu/dlt/](https://mjt.cs.illinois.edu/dlt/)}},  year = {2021},  note = {Version: 2021-10-27 v0.0-e7150f2d (alpha)}, }

**Basic setup: feedforward networks and test error decomposition**

In his section we outline our basic setup, which can be summarized as follows:

1. We consider standard shallow and deep feedforward networks.
2. We study mainly binary classification in the supervised learning setup.
3. As above, we study an error decomposition into three parts.

Although this means we exclude many settings, as discussed above, much of the work in other settings uses tools from this most standard one.

**Basic shallow network.** Consider the mapping

$$x\mapsto\sum_{j=1}^{m}a_{j}\sigma(w_{j}^{\intercal}x+b_{j}).$$

* \(\sigma\) is the _nonlinearity/activation/transfer_. Typical choices: ReLU \(z\mapsto\max\{0,z\}\), sigmoid \(z\mapsto\frac{1}{1+\exp(-z)}\).
* \(((a_{j},w_{j},b_{j}))_{j=1}^{m}\) are _trainable parameters_; varying them defines the function class. Sometimes in this shallow setting we freeze \((a_{j})_{j=1}^{m}\), which gives a simple model that is still difficult to analyze (e.g., nonconvex).
* We can think of this as a directed graph of _width_\(m\): we have a _hidden layer_ of \(m\) nodes, where the \(j\)th computes \(x\mapsto\sigma(w_{j}^{\intercal}x+b_{j})\).
* Define _weight_ matrix \(W\in\mathbb{R}^{m\times d}\) and _bias_ vector \(v\in\mathbb{R}^{m}\) as \(W_{j:}=w_{j}^{\intercal}\) and \(v_{j}:=b_{j}\). The first _layer_ computes \(h:=\sigma(Wx+b)\in\mathbb{R}^{m}\) (\(\sigma\) applied coordinate-wise), the second computes \(h\mapsto a^{\intercal}h\).

**Basic deep network.** Extending the matrix notation, given parameters \(w=(W_{1},b_{1},\ldots,W_{L},b_{L})\),

$$f(x;w):=\sigma_{L}(W_{L}\sigma_{L-1}(\cdots W_{2}\sigma_{1}(W_{1}x+b_{1})+b_{2 }\cdots)+b_{L}). \tag{1}$$

* \(\sigma_{j}\) is now a multivariate mapping; in addition to coordinate-wise ReLU and sigmoid, we can do _softmax_\(z^{\prime}\propto\exp(z)\), max-pooling (a few coordinates of input replaced with their maximum), attention layers, and many others.
* We can replace \(x\mapsto Wx+b\) with some compact representation while still preserving linearity, e.g., the standard implementation of a convolution layer. [ mjt(r): Maybe I will add the explicit formalisms somewhere?].

* Often biases \((b_{1},\ldots,b_{L})\) are dropped; the handling of these biases can change many elements of the story.
* Typically \(\sigma_{L}\) is identity, so we refer to \(L\) as the number of affine layers, and \(L-1\) the number of activation or hidden layers.
* Width now means the maximum output dimension of each activation. (For technical reasons, sometimes need to also take max or input dimension, or treat inputs as a fake layer.)
* Once again we can describe the computation via an acyclic graph. Classically, the activations were univariate mappings applied coordinate-wise, and single rows of the weight matrix were composed with univariate activations to give a _node_. Now, however, activations are often multivariate (and in particular can not be written as identical univariate mappings, applied coordinate-wise), and for computation reasons we prefer not to break the matrices into vectors, giving a more general graph with each matrix and activation as its own node.

**Basic supervised learning setup; test error decomposition.**

* Given pairs \(((x_{i},y_{i}))_{i=1}^{n}\) (training set), our job is to produce a mapping \(x\mapsto y\) which performs well on future examples.
* If there is no relationship between past and future data, we can't hope for much.
* The standard classical learning assumption is that both the training set, and future data, are drawn IID from some distribution on \((x,y)\).
* This IID assumption is _not practical_: it is not satisfied by real data. Even so, the analysis and algorithms here have many elements that carry over to more practical settings.

How do we define "performs well on future examples?"

* Given one \((x,y)\) and a prediction \(\hat{y}=f(x)\), we suffer a _loss_\(\ell(\hat{y},y)\), e.g., logistic \(\ln(1+\exp(-\hat{y}y))\), or squared \((\hat{y}-y)^{2}/2\).
* On a training set, we suffer _empirical risk_\(\widehat{\mathcal{R}}(f)=\frac{1}{n}\sum_{i}\ell(f(x_{i}),y_{i})\).
* For future (random!) data, we consider _(population) risk_\(\mathcal{R}(f)=\mathbb{E}\,\ell(f(x),y)=\int\ell(f(x),y)\mathrm{d}\mu(x,y)\).

"Performs well on future examples" becomes "minimize \(\mathcal{R}(f)\)." We can decompose \(\mathcal{R}(f)\) into three separate concerns: given a training algorithm's choice \(\hat{f}\) in some class of functions/predictors \(\mathcal{F}\), as well as some reference solution \(\bar{f}\in\mathcal{F}\),

$$\mathcal{R}(\hat{f}) =\mathcal{R}(\hat{f})-\widehat{\mathcal{R}}(\hat{f})$$ (generalization) $$\quad+\widehat{\mathcal{R}}(\hat{f})-\widehat{\mathcal{R}}(\bar{ f})$$ (optimization) $$\quad+\widehat{\mathcal{R}}(\bar{f})-\mathcal{R}(\bar{f})$$ (concentration/generalization) $$\quad+\mathcal{R}(\bar{f}).$$ (approximation)

These notes are organized are organized into separately considering these three terms (treating "generalization" and "concentration/generalization" together).

**Remark 0.2**: _(sensitivity to complexity)_ _As discussed, we aim to circumvent the aforementioned pitfalls by working with notions of low complexity model which work well with all three parts. There is still very little understanding of the right way to measure complexity, however here are some informal comments._* First suppose there exists a low complexity \(\bar{f}\in\mathcal{F}\) so that the **approximation term**\(\mathcal{R}(\bar{f})\) is small. Since the complexity is low, then the **concentration/generalization term**\(\widehat{\mathcal{R}}(\bar{f})-\mathcal{R}(\bar{f})\) is small.
* Since \(\bar{f}\) has low complexity, then hopefully we can find \(\hat{f}\) with not much larger complexity via an algorithm that balances the **optimization term**\(\widehat{\mathcal{R}}(\hat{f})-\widehat{\mathcal{R}}(\bar{f})\) with the complexity of \(\hat{f}\); if \(\hat{f}\) has low complexity, then the **generalization term**\(\mathcal{R}(\hat{f})-\widehat{\mathcal{R}}(\hat{f})\) will be small.

**Remark 0.3**: The two-argument form \(\ell(\hat{y},y)\) is versatile. We will most often consider binary classification \(y\in\{\pm 1\}\), where we always use the product \(\hat{y}y\), even for the squared loss:

$$\left[\hat{y}-y\right]^{2}=[y(y\hat{y}-1)]^{2}=(y\hat{y}-1)^{2}.$$

This also means binary classification networks have output dimension one, not two.

## Highlights

Here are a few of the shortened and/or extended proofs in these notes.

1. **Approximation.** * (Section 2.2) Succinct universal approximation via Stone-Weierstrass. * (Section 3) Succinct Barron's theorem (Fourier representation), with an explicit infinite width form. * (Section 5) Shorter depth separation proof.
2. **Optimization.** * (Section 8.1) Short re-proof of gradient flow convergence in the shallow NTK regime, due to [14]. * (Section 10.3) Short proof that smooth margins are non-decreasing for homogeneous networks; originally due to [15], this short proof is due to [16].
3. **Generalization.** * (Section 16.2) Shortened "spectrally-normalized bound" proof (P. Bartlett, Foster, and Telgarsky 2017). * (Section 17.3) Shortened ReLU network VC dimension proof.

## Missing topics and references

Due to the above philosophy, many topics are currently omitted. Over time I hope to fill the gaps. Here are some big omissions, hopefully resolved soon:

* Non-feedforward, e.g., recurrent [10].
* Specific feedforward architecture choices like convolutional layers and skip connections.
Continuous depth, for instance various neural ODE frameworks (R. T. Q. Chen et al. 2018; Tzen and Raginsky 2019).
* Other learning paradigms:
* Data augmentation, self-training, and distribution shift.
* Unsupervised learning (e.g., GANs), Adversarial ML, RL.

Further omitted topics, in a bit more detail, are discussed separately for approximation (section 1.1), optimization (section 6.1), and generalization (section 11.1).

### Acknowledgements

Thanks to Ziwei Ji for extensive comments, discussion, and the proof of Theorem 10.3; thanks to Daniel Hsu for extensive comments and discussion; thanks to Francesco Orabona for detailed comments spanning many sections; thanks to Ohad Shamir for extensive comments on many topics; thanks to Karolina Dziugaite and Dan Roy for extensive comments on the generalization material; thanks to Thien Nguyen for extensive and detailed comments and corrections on many sections. Further thanks to Nadav Cohen, Quanquan Gu, Suriya Gunasekar, Frederic Koehler, Justin Li, Akshayaa Magesh, Maxim Raginsky, David Rolnick, Kartik Sreenivasan, Matthieu Terris, and Alex Wozniakowski for various comments and feedback.

## 1 Approximation: preface

As above, we wish to ensure that our predictors \(\mathcal{F}\) (e.g., networks of a certain architecture) have some element \(\bar{f}\in\mathcal{F}\) which simultaneously has small \(\mathcal{R}(f)\) and small complexity; we can re-interpret our notation and suppose \(\mathcal{F}\) already is some constrained class of low-complexity predictors, and aim to make \(\inf_{f\in\mathcal{F}}\mathcal{R}(f)\) small.

What is \(\mathcal{F}\)?In keeping with the earlier theme, it should be some convenient notion of "low complexity model"; but what is that?

1. **Models reached by gradient descent.** Since standard training methods are variants of simple first-order methods, it seems this might be a convenient candidate for \(\mathcal{F}\) which is tight with practice. Unfortunately, firstly we only have understanding of these models very close to initialization and very late in training, whereas practice seems to lie somewhere between. Secondly, we can't just make this our definition as it breaks things in the standard approach to generalization.
2. **Models of low norm**, where norm is typically measured layer-wise, and also typically the "origin" is initialization. This is the current most common setup, though it doesn't seem to be able to capture the behavior of gradient descent that well, except perhaps when very close to initialization.
3. **All models of some fixed architecture**, meaning the weights can be arbitrary. This is the classical setup, and we'll cover it here, but it can often seem loose or insensitive to data, and was a key part of the criticisms against the general learning-theoretic approach (Zhang et al. 2017). The math is still illuminating and still key parts can be used as tools in a more sensitive analysis, e.g., by compressing a model and then applying one of these results.

The standard classical setup ("all models of some fixed architecture") is often stated with a goal of competing with all continuous functions:

$$\inf_{f\in\mathcal{F}}\mathcal{R}(f)\qquad\text{vs.}\qquad\inf_{g\text{ continuous}}\mathcal{R}(g).$$

E.g.,

$$\sup_{g\text{ cont.}\,f\in\mathcal{F}}\mathcal{R}(f)-\mathcal{R}(g).$$

To simplify further, if \(\ell\) is \(\rho\)-Lipschitz (and still \(y=\pm 1\)),

$$\mathcal{R}(f)-\mathcal{R}(g)=\int\left(\ell(yf(x))-\ell(yg(x)) \right)\mathrm{d}\mu(x,y)$$ $$\leq\int\rho|yf(x)-yg(x)|\mathrm{d}\mu(x,y)=\rho\int|f(x)-g(x)| \mathrm{d}\mu(x,y),$$

and in particular we have reduced the approximation question to one about studying \(\|f-g\|\) with function space norms.

**Remark 1.1**: **(Is this too strenuous?)** Most of the classical work uses the _uniform norm_: \(\|f-g\|_{u}=\sup_{x\in S}|f(x)-g(x)|\) where \(S\) is some compact set, and compares against continuous functions. Unfortunately, already if the target is Lipschitz continuous, this means our function class needs complexity which scales exponentially with dimension (Luxburg and Bousquet 2004): this highlights the need for more refined target functions and approximation measures.
**(Lower bounds.)** The uniform norm has certain nice properties for proving upper bounds, but is it meaningful for a lower bound? Functions can be well-separated in uniform norm even if they are mostly the same: they just need one point of large difference. For this reason, \(L_{1}\) norms, for instance \(\int_{[0,1]^{d}}|f(x)-g(x)|\mathrm{d}x\) are prefered for lower bounds.

**Remark 1.2**: While norms have received much recent attention as a way to measure complexity, this idea is quite classical. For instance, a resurgence of interest in the 1990s led to the proof of many deep network VC dimension bounds, however very quickly it was highlighted (and proved) in (P. L. Bartlett 1996) that one has situations where the architecture (and connection cardinality) stays fixed (along with the VC dimension), yet the norms (and generalization properties) vary.

**1.1**: **Omitted topics**

* Full proofs for sobolev space approximation (Yarotsky 2016; Schmidt-Hieber 2017). [ mjt(r): Planning to add in Fall 2021!!]
* Approximation of distributions and other settings.
* Approximation power of low-norm functions.

## 2 Classical approximations and "universal approximation"

We start with two types of standard approximation results, in the "classical" regime where we only care about the number of nodes and not the magnitude of the weights, and also the worst-case goal of competing with an arbitrary continuous function using some function space norm.

1. Elementary folklore results: univariate approximation with one hidden layer, and multivariate approximation with two hidden layers, just by stacking bricks. Latter use \(L_{1}\) metric, which is disappointing.
2. Celebrated "universal approximation" result: fitting continuous functions over compact sets in uniform norm with a single hidden layer (Hornik, Stinchcombe, and White 1989).

There are weaknesses in these results (e.g., curse of dimension), and thus they are far from the practical picture. Still, they are very interesting and influential.

**2.1 Elementary folklore constructions**

We can handle the univariate case by gridding the line and taking steps appropriately.

**Proposition 2.1**: Suppose \(g:\mathbb{R}\to\mathbb{R}\) is \(\rho\)-Lipschitz. For any \(\epsilon>0\), there exists a 2-layer network \(f\) with \(\lceil\frac{\rho}{\epsilon}\rceil\) threshold nodes \(z\mapsto\mathbf{1}[z\geq 0]\) so that \(\sup_{x\in[0,1]}|f(x)-g(x)|\leq\epsilon\).

**Proof.** Define \(m:=\lceil\frac{\rho}{\epsilon}\rceil\), and for and \(b_{i}:=i\epsilon/\rho\) for \(i\in\{0,\ldots,m-1\}\), and

$$a_{0}=g(0),\qquad a_{i}=g(b_{i})-g(b_{i-1}),$$

and lastly define \(f(x):=\sum_{i=0}^{m-1}a_{i}\mathbf{1}[x_{i}\geq b_{i}]\). Then for any \(x\in[0,1]\), letting \(k\) be the largest index so that \(b_{k}\leq x\), then \(f\) is constant along \([b_{k},x]\), and

$$|g(x)-f(x)| \leq|g(x)-g(b_{k})|+|g(b_{k})-f(b_{k})|+|f(b_{k})-f(x)|$$ $$\leq\rho|x-b_{k}|+\left|g(b_{k})-\sum_{i=0}^{k}a_{i}\right|+0$$ $$\leq\rho(\epsilon/\rho)+\left|g(b_{k})-g(b_{0})-\sum_{i=1}^{k}(g( b_{i})-g(b_{i-1}))\right|$$ $$=\epsilon.$$

**Remark 2.1**: This is standard, but we've lost something! We are paying for flat regions, which are a specialty of standard networks! A more careful proof only steps when it needs to and pays in _total variation_.

Now let's handle the multivariate case. We will replicate the univariate approach: we will increment function values when the target function changes. In the univariate case, we could "localize" function modifications, but in the multivariate case by default we will modify an entire halfspace at once. To get around this, we use an additional layer.

**Remark 2.2**:

* Note the problem is easy for finite point-sets: can reduce to univariate apx after projection onto a random line (homework 1?). But our goal is approximation over a _distribution_ of points.
* We will not get any nice theorem that says, roughly: "the exact complexity of shallow approximation depends on this function of the first \(\mathcal{O}(d)\) derivatives" (see also (Yarotsky 2016) for the deep case). This is part of why I like discussing the univariate case, where we have nice characterizations with total variation distance.

**Theorem 2.1**: Let continuous \(g:\mathbb{R}^{d}\to\mathbb{R}\) and an \(\epsilon>0\) be given, and choose \(\delta>0\) so that \(\|x-x^{\prime}\|_{\infty}\leq\delta\) implies \(|g(x)-g(x^{\prime})|\leq\epsilon\). Then there exists a 3-layer network \(f\) with \(\Omega(\frac{1}{\delta^{d}})\) ReLU with \(\int_{[0,1]^{d}}|f(x)-g(x)|\mathrm{d}x\leq 2\epsilon\).

**Remark 2.3**:
* Note the _curse of dimension_ (exponential dependence on \(d\), which also appears in lower bounds (Luxburg and Bousquet 2004)). Note CIFAR has \(d=3072\). This issue is inherent in approximating arbitrary continuous functions, and makes this irrelevant in practice.
* Construction also has large weights and Lipschitz constant.
* Later in Theorem 2.3 ((Hornik, Stinchcombe, and White 1989)) we'll give another approach that controls \(\sup_{x}|f(x)-g(x)|\) and uses only one activation layer, but it will not be a constructive proof, and trying to obtain estimates from it has all the preceding weaknesses as well.

The proof uses the following lemma (omitted in class), approximating continuous functions by piecewise constant functions.

**Lemma 2.1**: Let \(g,\delta,\epsilon\) be given as in Theorem 2.1. Let any set \(U\subset\mathbb{R}^{d}\) be given, along with a partition \(\mathcal{P}\) of \(U\) into rectangles (products of intervals) \(\mathcal{P}=(R_{1},\ldots,R_{N})\) with all side lengths not exceeding \(\delta\). Then there exist scalars \((\alpha_{1},\ldots,\alpha_{N})\) so that

$$\sup_{x\in U}|g(x)-h(x)|\leq\epsilon,\qquad\text{where}\qquad h=\sum_{i=1}^{N }\alpha_{i}\mathbf{1}_{R_{i}}.$$

**Proof.** Let partition \(\mathcal{P}=(R_{1},\ldots,R_{N})\) be given, and for each \(R_{i}\), pick some \(x_{i}\in R_{i}\), and set \(\alpha_{i}:=g(x_{i})\). Since each side length of each \(R_{i}\) is at most \(\delta\),

$$\sup_{x\in U}|g(x)-h(x)| =\sup_{i\in\{1,\ldots,N\}}\sup_{x\in R_{i}}|g(x)-h(x)|$$ $$\leq\sup_{i\in\{1,\ldots,N\}}\sup_{x\in R_{i}}\left(|g(x)-g(x_{i} )|+|g(x_{i})-h(x)|\right)$$ $$\leq\sup_{i\in\{1,\ldots,N\}}\sup_{x\in R_{i}}\left(\epsilon+|g(x _{i})-\alpha_{i}|\right)=\epsilon.$$

**Proof of Theorem 2.1.** For convenience, throughout this proof define a norm \(\|f\|_{1}=\int_{[0,2)^{d}}|f(x)|\mathrm{d}x\). Let \(\mathcal{P}\) denote a partition of \([0,2)^{d}\) into rectangles of the form \(\prod_{j=1}^{d}[a_{j},b_{j})\) with \(b_{j}-a_{j}\leq\delta\); the final result follows by restricting consideration to \([0,1]^{d}\), but we include an extra region to work with half-open intervals in a lazy way. Let \(h=\sum_{i}\alpha_{i}\mathbf{1}_{R_{i}}\) denote the piecewise-constant function provided by Lemma 2.1 with the given partition \(\mathcal{P}\), which satisfies \(\|g-h\|_{1}\leq\epsilon\). Our final network \(f\) will be of the form \(f(x):=\sum_{i}\alpha_{i}g_{i}(x)\), where each \(g_{i}\) will be a ReLU network with two hidden layers and \(\mathcal{O}(d)\) nodes; since \(|\mathcal{P}|\geq 1/\delta^{d}\), then \(f\) also uses at least \(1/\delta^{d}\) nodes as stated. Our goal is to show \(\|f-g\|_{1}\leq 2\epsilon\); to this end, note by the precedingchoices and the triangle inequality that

$$\|f-g\|_{1} \leq\|f-h\|_{1}+\|h-g\|_{1}$$ $$=\left\|\sum_{i}\alpha_{i}(\mathbf{1}_{R_{i}}-g_{i})\right\|_{1}+\epsilon$$ $$\leq\sum_{i}|\alpha_{i}|\cdot\|\mathbf{1}_{R_{i}}-g_{i}\|_{1}+\epsilon.$$

As such, if we can construct each \(g_{i}\) so that \(\|\mathbf{1}_{R_{i}}-g_{i}\|_{1}\leq\frac{\epsilon}{\sum_{i}|\alpha_{i}|}\), then the proof is complete. (If \(\sum_{i}|\alpha_{i}|=0\), we can set \(f\) to be the constant \(0\) network and the proof is again complete.)

Now fix \(i\) and let rectangle \(R_{i}\) be given of the form \(R_{i}:=\times_{j=1}^{d}[a_{j},b_{j})\), and define \(g_{i}\) as follows. Letting \(\gamma>0\) denote a free parameter to be optimized at the end of the proof, for each \(j\in\{1,\ldots,d\}\) define

$$g_{\gamma,j}(z) :=\sigma\left(\frac{z-(a_{j}-\gamma)}{\gamma}\right)-\sigma\left( \frac{z-a_{j}}{\gamma}\right)-\sigma\left(\frac{z-b_{j}}{\gamma}\right)+\sigma \left(\frac{z-(b_{j}+\gamma)}{\gamma}\right)$$ $$\in\begin{cases}\{1\}&z\in[a_{j},b_{j}],\\ \{0\}&x\not\in[a_{j}-\gamma,b_{j}+\gamma],\\ {[0,1]}&\text{otherwise},\end{cases}$$

and additionally

$$g_{\gamma}(x):=\sigma(\sum_{j}g_{\gamma,j}(x_{j})-(d-1)).$$

(Note that a second hidden layer is crucial in this construction, it is not clear how to proceed without it, certainly with only \(\mathcal{O}(d)\) nodes. Later proofs can use only a single hidden layer, but they are not constructive, and need \(\mathcal{O}(d)\) nodes.) Note that \(g_{\gamma}\approx\mathbf{1}_{R_{i}}\) as desired, specifically

$$g_{\gamma}(x)=\begin{cases}1&x\in R_{i},\\ 0&x\not\in\times_{j}[a_{j}-\gamma,b_{j}+\gamma],\\ {[0,1]}&\text{otherwise},\end{cases}$$

From which it follows that

$$\|g_{\gamma}(x)-\mathbf{1}_{R_{i}}(x)\|_{1} =\int_{R_{i}}|g_{\gamma}-\mathbf{1}_{R_{i}}|+\int_{\times_{j}[a_ {j}-\gamma,b_{j}+\gamma]\setminus R_{i}}|g_{\gamma}-\mathbf{1}_{R_{i}}|+\int_ {[0,2)^{d}\setminus\times_{j}[a_{j}-\gamma,b_{j}+\gamma]}|g_{\gamma}-\mathbf{1 }_{R_{i}}|$$ $$\leq 0+\prod_{j=1}^{d}(b_{j}-a_{j}+2\gamma)-\prod_{j=1}^{d}(b_{j} -a_{j})+0$$ $$\leq\mathcal{O}(\gamma),$$

which means we can ensure \(\|\mathbf{1}_{R_{i}}-g_{\gamma}\|_{1}\leq\frac{\epsilon}{\sum_{i}|\alpha_{i}|}\) by choosing sufficiently small \(\gamma\), which completes the proof.

**2.2 Universal approximation with a single hidden layer**The proof of Theorem 2.1 use two layers to construct \(g_{\gamma}\) such that \(g_{\gamma}(x)\approx\mathbf{1}\left[x\in\times_{i}[a_{i},b_{i}]\right]\). If instead we had a way to approximate multiplication we could instead approximate

$$x\mapsto\prod_{i}\mathbf{1}\left[x_{i}\in[a_{i},b_{i}]\right]=\mathbf{1}\left[x \in\times_{i}[a_{i},b_{i}]\right].$$

Can we do this and then form a linear combination, all with just one hidden layer?

The answer will be yes, and we will use this to resolve the classical _universal approximation_ question with a single hidden layer.

**Definition 2.1**: A class of functions \(\mathcal{F}\) is a _universal approximator_ over a compact set \(S\) if for every continuous function \(g\) and target accuracy \(\epsilon>0\), there exists \(f\in\mathcal{F}\) with

$$\sup_{x\in S}\left|f(x)-g(x)\right|\leq\epsilon.$$
**Remark 2.4**: Typically we will take \(S=[0,1]^{d}\); we can then reduce arbitrary compact sets to this case by defining a new function which re-scales the input. The compactness is in a sense necessary: as in the homework, consider approximating the sin function with a finite-size ReLU network over all of \(\mathbb{R}\). Lastly, universal approximation is often stated more succinctly as some class being dense in all continuous functions over compact sets.

Consider _unbounded width networks with one hidden layer:_

$$\mathcal{F}_{\sigma,d,m} :=\mathcal{F}_{d,m}:=\left\{x\mapsto a^{\mathrm{ T}}\sigma(Wx+b):a\in\mathbb{R}^{m},W\in\mathbb{R}^{m\times d},b\in\mathbb{R}^{m} \right\}.$$ $$\mathcal{F}_{\sigma,d} :=\mathcal{F}_{d}:=\bigcup_{m\geq 0}\mathcal{F}_{\sigma,d,m}.$$

Note that \(\mathcal{F}_{\sigma,m,1}\) denotes networks with a single node, and \(\mathcal{F}_{\sigma,d}\) is the linear span (in function space) of single-node networks.

First consider the (unusual) activation \(\sigma=\cos\). Since \(2\cos(y)\cos(z)=\cos(y+z)+\cos(y-z)\), then

$$2\left[\sum_{i=1}^{m}a_{i}\cos(w_{i}^{\mathrm{ T}}x+b_{i})\right]\cdot\left[\sum_{j=1}^{n}c_{j}\cos(u_{j}^{\mathrm{ T}}x+v_{j})\right]=$$ $$\sum_{i=1}^{m}\sum_{j=1}^{n}a_{i}c_{j}\left(\cos((w_{i}+u_{j})^{ \mathrm{ T}}x+(b_{i}+v_{j}))+\cos((w_{i}-u_{j})^{\mathrm{ T}}x+(b_{i}-v_{j}))\right),$$

thus \(f,g\in\mathcal{F}_{\cos,d}\Longrightarrow fg\in\mathcal{F}_{\cos,d}\)! In other words, \(\mathcal{F}_{\cos,d}\) is closed under multiplication, and since we know we can approximate univariate functions arbitrarily well, this suggests that we can approximate \(x\mapsto\prod_{i}\mathbf{1}\left[x_{i}\in[a_{i},b_{i}]\right]=\mathbf{1}\left[ x\in\times_{i}[a_{i},b_{i}]\right]\), and use it to achieve our more general approximation goal.

We're in good shape to give the general universal approximation result. The classical Weierstrass theorem establishes that polynomials are universal approximators (Weierstrass 1885), and its generalization, the Stone-Weierstrass theorem, says that any family of functions satisfying some of the same properties as polynomials will also be a universal approximator. Thus we will show \(\mathcal{F}_{\sigma,d}\) is a universal approximator via Stone-Weierstrass, a key step being closure under multiplication as above; this proof scheme was first suggested in (Hornik, Stinchcombe, and White 1989), but is now a fairly standard way to prove universal approximation.

First, here is the statement of the Stone-Weierstrass Theorem.

**Theorem 2.2**: _(Stone-Weierstrass; (Folland 1999, Theorem 4.45))_ Let functions \({\cal F}\) be given as follows.

1. Each \(f\in{\cal F}\) is continuous.
2. For every \(x\), there exists \(f\in{\cal F}\) with \(f(x)\neq 0\).
3. For every \(x\neq x^{\prime}\) there exists \(f\in{\cal F}\) with \(f(x)\neq f(x^{\prime})\) (\({\cal F}\)_separates points_).
4. \({\cal F}\) is closed under multiplication and vector space operations (\({\cal F}\) is an algebra).

Then \({\cal F}\) is a universal approximator: for every continuous \(g:{\mathbb{R}}^{d}\to{\mathbb{R}}\) and \(\epsilon>0\), there exists \(f\in{\cal F}\) with \(\sup_{x\in[0,1]^{d}}|f(x)-g(x)|\leq\epsilon\).

**Remark 2.5**:

* This is a heavyweight tool, but a convenient way to quickly check universal approximation.
* Proofs are not constructive, but the size lower bound \(\Omega(\frac{1}{e^{2}})\) seems to naturally appear in various places; e.g., to show closure under products as above, we double (or more) the number of terms for each dimension.
* Weierstrass theorem itself has interesting proofs:
* The modern standard one is due to Bernstein; it picks a fine grid and then a convenient set of interpolating polynomials which behave stably off the grid.
* Weierstrass's original proof convolved the target with a Gaussian, which makes it analytic, and also leads to good polynomial approximation.
* The second and third conditions in Stone-Weierstrass are necessary; if there exists \(x\) so that \(f(x)=0\forall f\in{\cal F}\), then we can't approximate \(g\) with \(g(x)\neq 0\); if we can't separate points \(x\neq x^{\prime}\), then we can't approximate functions with \(g(x)\neq g(x^{\prime})\).

First, we go back to cos activations, which was the original choice in (Hornik, Stinchcombe, and White 1989); we can then handle arbitrary activations by univariate approximation of cos, without increasing the depth (but increasing the width).

**Lemma 2.2**: _((Hornik, Stinchcombe, and White 1989))_\({\cal F}_{\rm cos,d}\) is universal.

**Proof.** Let's check the Stone-Weierstrass conditions:

1. Each \(f\in{\cal F}_{\rm cos,d}\) is continuous.

2. For each \(x\), \(\cos(0^{\mbox{\tiny T}}x)=1\neq 0\).

3. For each \(x\neq x^{\prime}\), \(f(z):=\cos((z-x^{\prime})^{\mbox{\tiny T}}(x-x^{\prime})/\|x-x^{\prime}\|^{2}) \in{\cal F}_{d}\) satisfies

$$f(x)=\cos(1)\neq\cos(0)=f(x^{\prime}).$$

4. \({\cal F}_{\rm cos,d}\) is closed under products and vector space operations as before.

We can work it out even more easily for \({\cal F}_{\rm exp,d}\).

**Lemma 2.3**: \({\cal F}_{\rm exp,d}\) is universal.

**Proof.** Let's check the Stone-Weierstrass conditions:

1. Each \(f\in{\cal F}_{\rm exp,d}\) is continuous.

2. For each \(x\), \(\exp(0^{\mbox{\tiny T}}x)=1\neq 0\).

3. For each \(x\neq x^{\prime}\), \(f(z):=\exp((z-x^{\prime})^{\tau}(x-x^{\prime})/\|x-x^{\prime}\|^{2})\in{\cal F}_{d}\) satisfies $$f(x)=\exp(1)\neq\exp(0)=f(x^{\prime}).$$
4. \({\cal F}_{\exp,d}\) is closed under VS ops by construction; for products, $$\left(\sum_{i=1}^{n}r_{i}\exp(a_{i}^{\tau}x)\right)\left(\sum_{j=1}^{m}s_{j} \exp(b_{j}^{\tau}x)\right)=\sum_{i=1}^{m}\sum_{j=1}^{m}r_{i}s_{j}\exp((a+b)^{ \tau}x).$$

Now let's handle arbitrary activations.

**Theorem 2.3**_((Hornik, Stinchcombe, and White 1989))_ Suppose \(\sigma:\mathbb{R}\rightarrow\mathbb{R}\) is _sigmoidal_: it is continuous, and

$$\lim_{z\rightarrow-\infty}\sigma(z)=0,\qquad\lim_{z\rightarrow+\infty}\sigma (z)=1.$$

Then \({\cal F}_{\sigma,d}\) is universal.

**Proof sketch** (details in hw1). Given \(\epsilon>0\) and continuous \(g\), use Lemma 2.2 ((Hornik, Stinchcombe, and White 1989)) (or Lemma 2.3) to obtain \(h\in{\cal F}_{\cos,d}\) (or \({\cal F}_{\exp,d}\)) with \(\sup_{x\in[0,1]^{d}}|h(x)-g(x)|\leq\epsilon/2\). To finish, replace all appearances of \(\cos\) with an element of \({\cal F}_{\sigma,1}\) so that the total additional error is \(\epsilon/2\).

**Remark 2.6**

* ReLU is fine: use \(z\mapsto\sigma(z)-\sigma(z-1)\) and split nodes.
* exp didn't need bias in the proof, but this seems natural due to \(\exp(a^{\tau}x+b)=e^{b}\cdot\exp(a^{\tau}x)\). On the other hand, approximating exp with ReLU uses bias terms, so we don't obtain a trick via exp to remove biases in general.
* Weakest conditions on \(\sigma\) (Leshno et al. 1993): universal apx iff **not** a polynomial.
* Carefully accounting within the proof seems to indicate curse of dimension again (size \(\Omega(\frac{1}{\epsilon^{d}})\)), due for instance to expanding all terms in a product of \(d\) terms.

**Remark 2.7**_(other universal approximation proofs)_

* (Cybenko 1989) Assume contradictorily you miss some functions. By duality, \(0=\int\sigma(a^{\tau}x-b)\mathrm{d}\mu(x)\) for some signed measure \(\mu\), all \((a,b)\). Using Fourier, can show this implies \(\mu=0\ldots\)
* (Leshno et al. 1993) If \(\sigma\) a polynomial,...; else can (roughly) get derivatives and polynomials of all orders (we'll have homework problems on this).
* (Barron 1993) Use inverse Fourier representation to construct an infinite-width network; we'll cover this next. It can beat the worst-case curse of dimension!
* (Funahashi 1989) [ mjt(c): I'm sorry, I haven't read it. Also uses Fourier.]

## 3 Infinite-width Fourier representations and the Barron norm

This section presents two ideas which have recently become very influential again.

1. Using infinite-width networks. This may seem complicated, but in fact it simplifies many things, and better captures certain phenomena.
2. Barron's approximation theorem and norm (Barron 1993). Barron's original goal was an approximation result which requires few nodes in some favorable cases. Interestingly, his construction can be presented as an infinite-width representation _with equality_, and furthermore the construction gives approximation guarantees near initialization (e.g., for the NTK, the topic of the next section).

We will finish the section with a more general view of these infinite-width constructions, and a technique to sample finite-width networks from them.

**3.1 Infinite-width univariate approximations**

Let's warm up with some univariate constructions.

**Proposition 3.1**: Suppose \(g:\mathbb{R}\to\mathbb{R}\) is differentiable, and \(g(0)=0\). If \(x\in[0,1]\), then \(g(x)=\int_{0}^{1}\mathbf{1}[x\geq b]g^{\prime}(b)\mathrm{d}b\).

**Proof.** By FTC and \(g(0)=0\) and \(x\in[0,1]\),

$$g(x)=g(0)+\int_{0}^{x}g^{\prime}(b)\mathrm{d}b=0+\int_{0}^{1}\mathbf{1}[x\geq b ]g^{\prime}(b)\mathrm{d}b.$$

That's really it! We've written a differentiable function as a shallow infinite-width network, _with equality_, effortlessly.

**Remark 3.1**: In the last subsection, when we sample from infinite-width networks, The error for this univariate case will scale with \(\int_{0}^{1}|g^{\prime}(x)|\mathrm{d}x\). This quantity is adaptive, e.g., correctly not paying for flat regions, which was discussed after our basic grid-based univariate approximation in Proposition 2.1. As mentioned before, this is a big point of contrast with polynomial approximation.

**3.2 Barron's construction for infinite-width multivariate approximation**

This approach uses Fourier transforms; for those less familiar, it might seem daunting, but:

* The approach will turn out to be natural.
* There is extensive literature on Fourier transforms, so it's an important connection to make.
* The original paper (Barron 1993) is over 30 years old now, and still this seems to be one of the best approaches, even with modern considerations like staying near initialization!

Let's first argue it's natural. Recall the Fourier transform (e.g., Folland 1999, Chapter 8):

$$\hat{f}(w):=\int\exp(-2\pi iw^{\top}x)f(x)\mathrm{d}x.$$

We also have Fourier inversion: if \(f\in L^{1}\) and \(\hat{f}\in L^{1}\),

$$f(x)=\int\exp(2\pi iw^{\top}x)\hat{f}(w)\mathrm{d}w.$$The inversion formula rewrite \(f\) as an infinite-width network! The only catch is that the activations are not only non-standard, they are over the complex plane.

**Remark 3.2**: Unfortunately, there are different conventions for the Fourier transform (in fact, the original work we reference uses a different one (Barron 1993)).

Barron's aproach is to convert these activations into something more normal; here we'll use threshold nodes, but others are fine as well. If our starting function \(f\) is over the reals, then using \(\Re\) to denote the real part of a complex number, meaning \(\Re(a+bi)=a\), then

$$f(x)=\Re f(x)=\int\Re\exp(2\pi iw^{\mathsf{T}}x)\hat{f}(w)\mathrm{d}w.$$

If we expand with \(e^{iz}=\cos(z)+i\sin(z)\), we're left with \(\cos\), which is not compactly supported; to obtain an infinite-width form with threshold gates using a density which is compactly supported, Barron uses two tricks.

1. **Polar decomposition.** Let's split up the Fourier transform \(\hat{f}\) into magnitude and radial parts: write \(\hat{f}(w)=|\hat{f}(w)|\exp(2\pi i\theta(w))\) with \(|\theta(w)|\leq 1\). Since \(f\) is real-valued, $$f(x) =\Re\int\exp(2\pi iw^{\mathsf{T}}x)\hat{f}(w)\mathrm{d}w$$ $$=\int\Re\left(\exp(2\pi iw^{\mathsf{T}}x)\exp(2\pi i\theta(w))| \hat{f}(w)|\right)\mathrm{d}w$$ $$=\int\Re\left(\exp(2\pi iw^{\mathsf{T}}x+2\pi i\theta(w))\,|\hat{ f}(w)|\mathrm{d}w\right.$$ We've now obtained an infinite width network over real-valued activations! \(\cos\) is neither compactly supported, no approaches a limit as its argument goes \(\pm\infty\), which is where Barron's second trick comes in.
2. **Turning cosines into bumps!** We'll do two things to achieve our goal: subtracting \(f(0)\), and scaling by \(\|w\|\): $$f(x)-f(0)$$ $$=\int\left[\cos(2\pi w^{\mathsf{T}}x+2\pi\theta(w))-\cos(2\pi w^{ \mathsf{T}}0+2\pi\theta(w))\right]|\hat{f}(w)|\mathrm{d}w$$ $$=\int\frac{\cos(2\pi w^{\mathsf{T}}x+2\pi\theta(w))-\cos(2\pi \theta(w))}{\|w\|}\|w\|\cdot|\hat{f}(w)|\mathrm{d}w.$$ The fraction does not blow up: since \(\cos\) is \(1\)-Lipschitz, $$\left|\frac{\cos(2\pi w^{\mathsf{T}}x+2\pi\theta(w))-\cos(2\pi \theta(w))}{\|w\|}\right|$$ $$\leq\frac{|2\pi w^{\mathsf{T}}x+2\pi\theta(w)-2\pi\theta(w)|}{\|w \|}\leq\frac{2\pi|w^{\mathsf{T}}x|}{\|w\|}\leq 2\pi\|x\|.$$ This quantity is therefore well-behaved for bounded \(\|x\|\) so long as \(\|w\|\|\hat{f}(w)\|\) is well-behaved. Barron combined these ideas with the sampling technique in Lemma 3.1 (Maurey (Pisier 1980)) to obtain estimates on the number of nodes needed to approximate functions whenever \(\|w\|\cdot|\hat{f}(w)|\)is well-behaved. We will follow a simpler approach here: we will give an explicit infinite-width form via only the first trick above and some algebra, and only then invoke sampling. The quantity \(\|w\|\cdot|\hat{f}(w)|\) will appear in the estimate of the "mass" of the infinite-width network as used to estimate how much to sample, analogous to the quantity \(\int_{0}^{1}|g^{\prime}(x)|\mathrm{d}x\) from Proposition 2.1.

Before continuing, let's discuss \(\|w\|\cdot|\hat{f}(w)|\) a bit more, which can be simplified via \(\widehat{\nabla f}(w)=2\pi iw\hat{f}(w)\) into a form commonly seen in the literature.

**Definition 3.1**: The quantity

$$\int\left\|\widehat{\nabla f}(w)\right\|\mathrm{d}w=2\pi\int\|w\|\cdot|\hat{f} (w)|\mathrm{d}w$$

is the _Barron norm_ of a function \(f\). The corresponding _Barron class with norm_\(C\) is

$$\mathcal{F}_{C}:=\left\{f:\mathbb{R}^{d}\rightarrow\mathbb{R}\quad:\quad\hat{f }\text{ exists},\int\left\|\widehat{\nabla f}(w)\right\|\mathrm{d}w\leq C \right\}.$$
**Remark 3.3**: Barron's approximation bounds were on \(\mathcal{F}_{C}\), and in particular the number of nodes needed scaled with \(C/\epsilon^{2}\), where \(\epsilon\) is the target accuracy. As we will see later, since threshold units are (kindof) the derivatives of ReLUs, then the Barron norm can also be used for complexity estimates of shallow networks near initialization (the NTK regime) (Ji, Telgarsky, and Xian 2020). [ mjt(r): My friend Daniel Hsu told me that related ideas are in (Bach 2017) as well, though I haven't read closely and fleshed out this connection yet.]

Here is our approach in detail. Continuing with the previous Barron representation and using \(\|x\|\leq 1\),

$$\cos(2\pi w^{\mathsf{T}}x+2\pi\theta(w))-\cos(2\pi\theta(w)) =\int_{0}^{w^{\mathsf{T}}x}-2\pi\sin(2\pi b+2\pi\theta(w))\mathrm{ d}b$$ $$=-2\pi\int_{0}^{\|w\|}\mathbf{1}[w^{\mathsf{T}}x-b\geq 0]\sin(2 \pi b+2\pi\theta(w))\mathrm{d}b$$ $$+2\pi\int_{-\|w\|}^{0}\mathbf{1}[-w^{\mathsf{T}}x+b\geq 0]\sin(2 \pi b+2\pi\theta(w))\mathrm{d}b.$$

Plugging this into the previous form (before dividing by \(\|w\|\)),

$$f(x)-f(0) =-2\pi\int\!\!\int_{0}^{\|w\|}\mathbf{1}[w^{\mathsf{T}}x-b\geq 0] \left[\sin(2\pi b+2\pi\theta(w))|\hat{f}(w)|\right]\mathrm{d}b\mathrm{d}w$$ $$+2\pi\int\!\!\int_{-\|w\|}^{0}\mathbf{1}[-w^{\mathsf{T}}x+b\geq 0 ]\left[\sin(2\pi b+2\pi\theta(w))|\hat{f}(w)|\right]\mathrm{d}b\mathrm{d}w,$$

an infinite width network with threshold nodes!

We'll tidy up with \(\widehat{\nabla f}(w)=2\pi iw\hat{f}(w)\) whereby \(\|\widehat{\nabla f}(w)\|=2\pi\|w\|\cdot|\hat{f}(w)|\) as mentioned before. Lastly, to estimate the "mass" of this infinite width network (the integral of the density part of the integrand),

$$\left|2\pi\int\!\!\!\int_{0}^{\|w\|}\left[\sin(2\pi b+2\pi\theta(w))| \hat{f}(w)|\right]\mathrm{d}b\mathrm{d}w\right|$$ $$+\left|2\pi\int\!\!\!\int_{-\|w\|}^{0}\left[\sin(2\pi b+2\pi \theta(w))|\hat{f}(w)|\right]\mathrm{d}b\mathrm{d}w\right|$$ $$\leq 2\pi\int\!\!\!\int_{-\|w\|}^{\|w\|}|\sin(2\pi b+2\pi\theta(w) )|\,|\hat{f}(w)|\mathrm{d}b\mathrm{d}w$$ $$\leq 2\pi\int 2\|w\|\cdot|\hat{f}(w)|\mathrm{d}b\mathrm{d}w$$ $$=2\int\left\|\widehat{\nabla f}(w)\right\|\mathrm{d}w.$$

Summarizing this derivations gives the following version of Barron's approach.

**Theorem 3.1** (**based on (Barron 1993))**: _Suppose \(\int\left\|\widehat{\nabla f}(w)\right\|\mathrm{d}w<\infty\), \(f\in L_{1}\), \(\hat{f}\in L_{1}\), and write \(\hat{f}(w)=|\hat{f}(w)|\exp(2\pi i\theta(w))\). For \(\|x\|\leq 1\),_

$$f(x)-f(0)=\int\frac{\cos(2\pi w^{\mathrm{ T}}x+2\pi\theta(w))-\cos(2\pi\theta(w))}{2\pi\|w\|}\left\|\widehat{\nabla f }(w)\right\|\mathrm{d}w$$ $$=-2\pi\int\!\!\!\int_{0}^{\|w\|}\mathbf{1}[w^{\mathrm{ T}}x-b\geq 0]\left[\sin(2\pi b+2\pi\theta(w))|\hat{f}(w)|\right]\mathrm{d}b \mathrm{d}w$$ $$\quad+2\pi\int\!\!\!\int_{-\|w\|}^{0}\mathbf{1}[-w^{\mathrm{ T}}x+b\geq 0]\left[\sin(2\pi b+2\pi\theta(w))|\hat{f}(w)|\right]\mathrm{d}b \mathrm{d}w.$$

The corresponding measure on weights has mass at most

$$2\int\left\|\widehat{\nabla f}(w)\right\|\!\!\mathrm{d}w.$$

When combined with the sampling tools in 3.3, we will recover Barron's full result that the number of nodes needed to approximate \(f\) to accuracy \(\epsilon>0\) is roughly \(\left\|\widehat{\nabla f}(w)\right\|\!\!\mathrm{d}w/\epsilon^{2}\).

Ideally, the Barron norm is small, for instance polynomial (rather than exponential) in dimension for interesting examples. Here are a few, mostly taken from (Barron 1993).

* **Gaussians.** Since (e.g., Folland 1999, Prop 8.24) $$f(x)=(2\pi\sigma^{2})^{d/2}\exp(-\frac{\|x\|^{2}}{2\sigma^{2}})$$ $$\implies\hat{f}(w)=\exp(-2\pi^{2}\sigma^{2}\|w\|^{2}),$$ meaning \(\hat{f}\) is an unnormalized Gaussian with variance \((4\pi^{2}\sigma^{2})^{-1}\). Using normalization \(Z=(2\pi\sigma^{2})^{-d/2}\) and Holder gives $$\int\|w\|\|\hat{f}(w)|\mathrm{d}w =Z\int Z^{-1}\|w\|\|\hat{f}(w)|\mathrm{d}w$$ $$\leq Z\left(\int Z^{-1}\|w\|^{2}|\hat{f}(w)|\mathrm{d}w\right)^{1/2}$$ $$=Z\left(\frac{d}{4\pi^{2}\sigma^{2}}\right)^{1/2}=\frac{\sqrt{d}} {\sqrt{2\pi}(2\pi\sigma^{2})^{(d+1)/2}}.$$Consequently, if \(2\pi\sigma^{2}\geq 1\), then \(\int\left\|\widehat{\nabla f}(w)\right\|{\rm d}w={\cal O}(\sqrt{d})\). On the other hand, general radial functions have exponential \(\left\|\widehat{\nabla f}(w)\right\|\) (Comment IX.9, Barron 1993); this is circumvented here since \(\left\|x\right\|\leq 1\) and hence the Gaussian is quite flat.
* Further brief example \(\int\left\|\widehat{\nabla f}(w)\right\|{\rm d}w\) calculations:
* A few more from (Barron 1993, sec. IX): radial functions (IX.9), compositions with polynomials (IX.12) and analytic functions (IX.13), functions with \({\cal O}(d)\) bounded derivatives (IX.15).
* Barron also gives a lower bound for a specific set of functions which is exponential in dimension.
* Further comments on Barron's constructions can be found in (H. Lee et al. 2017).
* General continuous functions can fail to satisfy \(\int\left\|\widehat{\nabla f}(w)\right\|{\rm d}w<\infty\), but we can first convolve them with Gaussians and sample the resulting nearby function; this approach, along with a Barron theorem using ReLUs, can be found in (Ji, Telgarsky, and Xian 2020).

**3.3 Sampling from infinite width networks**

Now we will show how to obtain a finite-width representation from an infinite-width representation. Coarsely, given a representation \(\int\sigma(w^{\rm T}x)g(w){\rm d}w\), we can form an estimate

$$\sum_{j=1}^{m}s_{j}\tilde{\sigma}(w_{j}^{\rm T}x),\qquad\mbox{where }s_{j} \in\pm 1,\ \tilde{\sigma}(z)=\sigma(z)\int|g(w)|{\rm d}w,$$

by sampling \(w_{j}\sim|g(w)|/\int|g(w)|{\rm d}w\), and letting \(s_{j}:={\rm sgn}(g(w_{j}))\), meaning the sign corresponding to whether \(w\) fell in a negative or positive region of \(g\). In expectation, this estimate is equal to the original function.

Here we will give a more general construction where the integral is not necessarily over the Lebesgue measure, which is useful when it has discrete parts and low-dimensional sets. This section will follow the same approach as (Barron 1993), namely using Maurey's sampling method (cf. Lemma 3.1 (Maurey (Pisier 1980))), which gives an \(L_{2}\) error; it is possible to use these techniques to obtain an \(L_{\infty}\) error via the "co-VC dimension technique" (Gurvits and Koiran 1995), but this is not pursued here.

To build this up, first let us formally define these infinite-width networks and their mass.

**Definition 3.2**: An _infinite-width shallow network_ is characterized by a _signed measure_\(\nu\) over weight vectors in \({\mathbb{R}}^{p}\):

$$x\mapsto\int\sigma(w^{\rm T}x){\rm d}\nu(w).$$

The _mass_ of \(\nu\) is the total positive and negative weight mass assigned by \(\nu\): \(|\nu|({\mathbb{R}}^{p})=\nu_{-}({\mathbb{R}}^{p})+\nu_{+}({\mathbb{R}}^{p})\).
**Remark 3.4**: We can connect this to the initial discussion of \(\int\sigma(w^{\rm T}x)g(w){\rm d}w\) by defining a signed measure \(\nu\) via \({\rm d}\nu=g\), and the mass is once again \(|\nu|({\mathbb{R}}^{p})=\int|g(w)|{\rm d}w\), and the positive and negative parts \(\nu_{-}\) and \(\nu_{+}\) are simply the regions where \(g\) is respectively negative (or just non-positive) and positive.

In the case of general measures, a decomposition into \(\nu_{-}\) and \(\nu_{+}\) is guaranteed to exist (Jordan decomposition, Folland 1999), and is unique up to null sets.

The notation here uses \(\mathbb{R}^{p}\) not \(\mathbb{R}^{d}\) since we might bake in biases and other feature mappings.

To develop sampling bounds, first we give the classical general Maurey sampling technique, which is stated as sampling in Hilbert spaces.

Suppose \(X=\mathbb{E}\,V\), where r.v. \(V\) is supported on a set \(S\). A natural way to "simplify" X is to instead consider \(\hat{X}:=\frac{1}{k}\sum_{i=1}^{k}V_{i}\), where \((V_{1},\ldots,V_{k})\) are sampled iid. We want to argue \(\hat{X}\approx X\); since we're in a Hilbert space, we'll try to make the Hilbert norm \(\left\|X-\hat{X}\right\|\) small.

**Lemma 3.1**: _(Maurey (Pisier 1980))_ Let \(X=\mathbb{E}\,V\) be given, with \(V\) supported on \(S\), and let \((V_{1},\ldots,V_{k})\) be iid draws from the same distribution. Then

$$\mathop{\mathbb{E}}_{V_{1},\ldots,V_{k}}\left\|X-\frac{1}{k}\sum_{i}V_{i} \right\|^{2}\leq\frac{\mathbb{E}\left\|V\right\|^{2}}{k}\leq\frac{\sup_{U\in S }\left\|U\right\|^{2}}{k},$$

and moreover there exist \((U_{1},\ldots,U_{k})\) in \(S\) so that

$$\left\|X-\frac{1}{k}\sum_{i}U_{i}\right\|^{2}\leq\mathop{\mathbb{E}}_{V_{1}, \ldots,V_{k}}\left\|X-\frac{1}{k}\sum_{i}V_{i}\right\|^{2}.$$

**Remark 3.5** After proving this, we'll get a corollary for sampling from networks.

This lemma is widely applicable; e.g., we'll use it for generalization too.

First used for neural networks by (Barron 1993) and (Jones 1992), attributed to Maurey by (Pisier 1980).

**Proof of Lemma 3.1** (Maurey (Pisier 1980)).: Let \((V_{1},\ldots,V_{k})\) be IID as stated. Then

$$\mathop{\mathbb{E}}_{V_{1},\ldots,V_{k}}\left\|X-\frac{1}{k}\sum_ {i}V_{i}\right\|^{2}$$ $$=\mathop{\mathbb{E}}_{V_{1},\ldots,V_{k}}\left\|\frac{1}{k}\sum_ {i}\left(V_{i}-X\right)\right\|^{2}$$ $$=\mathop{\mathbb{E}}_{V_{1},\ldots,V_{k}}\frac{1}{k^{2}}\left[ \sum_{i}\left\|V_{i}-X\right\|^{2}+\sum_{i\neq j}\left\langle V_{i}-X,V_{j}-X \right\rangle\right]$$ $$=\mathop{\mathbb{E}}_{V}\frac{1}{k}\left\|V-X\right\|^{2}$$ $$=\mathop{\mathbb{E}}_{V}\frac{1}{k}\left(\left\|V\right\|^{2}- \left\|X\right\|^{2}\right)$$ $$\leq\mathop{\mathbb{E}}_{V}\frac{1}{k}\left\|V\right\|^{2}\leq \sup_{U\in S}\frac{1}{k}\left\|U\right\|^{2}.$$

To conclude, there must exist \((U_{1},\ldots,U_{k})\) in \(S\) so that \(\left\|X-k^{-1}\sum_{i}U_{i}\right\|^{2}\leq\mathop{\mathbb{E}}_{V_{1},\ldots, V_{k}}\left\|X-k^{-1}\sum_{i}V_{i}\right\|^{2}\). ("Probabilistic method.")

Now let's apply this to infinite-width networks in the generality of Definition 3.2. We have two issues to resolve.

* **Issue 1:*
* what is the appropriate Hilbert space?
* We'll use \(\langle f,g\rangle=\int f(x)g(x)\mathrm{d}P(x)\) for some probability measure \(P\) on \(x\), so \(\|f\|_{L_{2}(P)}^{2}=\int f(x)^{2}\mathrm{d}P(x)\).
* **Issue 2:*
* our "distribution" on weights is not a probability!
* consider \(x\in[0,1]\) and \(\sin(2\pi x)=\int_{0}^{1}\mathbf{1}[x\geq b]2\pi\cos(2\pi b)\mathrm{d}b\). There are two issues: \(\int_{0}^{1}|2\pi\cos(2\pi b)|\mathrm{d}b\neq 1\), and \(\cos(2\pi b)\) takes on negative and positive values.
* we'll correct this in detail shortly, but here is a sketch; recall also the discussion in Definition 3.2 of splitting a measure into positive and negative parts. First, we introduce a fake parameter \(s\in\{\pm 1\}\) and multiply \(\mathbf{1}[x\geq b]\) with it, simulating positive and negative weights with only positive weights; now our distribution is on pairs \((s,b)\). Secondly, we'll normalize everything by \(\int_{0}^{1}|2\pi\cos(2\pi b)|\mathrm{d}b\).

Let's write a generalized shallow network as \(x\mapsto\int g(x;w)\mathrm{d}\mu(w)\), where \(\mu\) is a nonzero signed measure over some abstract parameter space \(\mathbb{R}^{p}\). E.g., \(w=(a,b,v)\) and \(g(x;w)=a\sigma(v^{\mathrm{ T}}x+b)\).

* Decompose \(\mu=\mu_{+}-\mu_{-}\) into nonnegative measures \(\mu_{\pm}\) with disjoint support (this is the _Jordan decomposition_(Folland, 1999), which was mentioned in Definition 3.2).
* For nonnegative measures, define total mass \(\|\mu_{\pm}\|_{1}=\mu_{\pm}(\mathbb{R}^{p})\), and otherwise \(\|\mu\|_{1}=\|\mu_{+}\|_{1}+\|\mu_{-}\|_{1}\).
* Define \(\widetilde{\mu}\) to sample \(s\in\{\pm 1\}\) with \(\Pr[s=+1]=\frac{\|\mu_{+}\|_{1}}{\|\mu\|_{1}}\), and then sample \(g\sim\frac{\mu_{s}}{\|\mu_{s}\|_{1}}=:\widetilde{\mu}_{s}\), and output \(\tilde{g}(\cdot;w,s)=s\|\mu\|_{1}g(\cdot;w)\).

This sampling procedure has the correct mean:

**Lemma 3.2** (**Maurey for signed measures)**: Let \(\mu\) denote a nonzero signed measure supported on \(S\subseteq\mathbb{R}^{p}\), and write \(g(x):=\int g(x;w)\mathrm{d}\mu(w)\). Let \((\tilde{w}_{1},\ldots,\tilde{w}_{k})\) be IID draws from the corresponding \(\widetilde{\mu}\), and let \(P\) be a probability measure on \(x\). Then

$$\mathop{\mathbb{E}}_{\tilde{w}_{1},\ldots,\tilde{w}_{k}}\left\|g- \frac{1}{k}\sum_{i}\tilde{g}(\cdot;\tilde{w}_{i})\right\|_{L_{2}(P)}^{2} \leq\frac{\mathbb{E}\left\|\tilde{g}(\cdot;\tilde{w})\right\|_{L_ {2}(P)}^{2}}{k}$$ $$\leq\frac{\|\mu\|_{1}^{2}\sup_{w\in S}\|g(\cdot;w)\|_{L_{2}(P)}^{ 2}}{k},$$

and moreover there exist \((w_{1},\ldots,w_{k})\) in \(S\) and \(s\in\{\pm 1\}^{m}\) with

$$\left\|g-\frac{1}{k}\sum_{i}\tilde{g}(\cdot;w_{i},s_{i})\right\|_{L_{2}(P)}^{ 2}\leq\mathop{\mathbb{E}}_{\tilde{w}_{1},\ldots,\tilde{w}_{k}}\left\|g-\frac {1}{k}\sum_{i}\tilde{g}(\cdot;\tilde{w}_{i})\right\|_{L_{2}(P)}^{2}.$$

**Proof.** By the mean calculation we did earlier, \(g=\mathbb{E}_{\widetilde{\mu}}\|\mu\|sg_{w}=\mathbb{E}_{\widetilde{\mu}}\tilde{g}\), so by the regular Maurey applied to \(\widetilde{\mu}\) and Hilbert space \(L_{2}(P)\) (i.e., writing \(V:=\tilde{g}\) and \(g=\mathbb{E}\,V\)),

$$\mathbb{E}_{\widetilde{\mu}_{1},\ldots,\widetilde{w}_{k}}\left\|g- \frac{1}{k}\sum_{i}\tilde{g}(\cdot;\widetilde{w}_{i})\right\|_{L_{2}(P)}^{2} \leq\frac{\mathbb{E}\left\|\tilde{g}(\cdot;\widetilde{w})\right\| _{L_{2}(P)}^{2}}{k}$$ $$\leq\frac{\sup_{s\in\{\pm 1\}}\sup_{w\in\mathcal{W}}\left\{\|\mu\|_{ 1}sg(\cdot;w)\right\}_{L_{2}(P)}^{2}}{k}.$$ $$\leq\frac{\|\mu\|_{1}^{2}\sup_{w\in S}\|g(\cdot;w)\|_{L_{2}(P)}^{ 2}}{k},$$

and the existence of the fixed \((w_{i},s_{i})\) is also from Maurey.

**Example 3.1**: _(various infinite-width sampling bounds)_

1. Suppose \(x\in[0,1]\) and \(f\) is differentiable. Using our old univariate calculation, $$f(x)-f(0)=\int_{0}^{1}\mathbf{1}[x\geq b]f^{\prime}(b)\mathrm{d}b.$$ Let \(\mu\) denote \(f^{\prime}(b)\mathrm{d}b\); then a sample \(((b_{i},s_{i}))_{i=1}^{k}\) from \(\widetilde{\mu}\) satisfies $$\left\|f(\cdot)-f(0)-\frac{\|\mu\|_{1}}{k}\sum_{i}s_{i}\mathbf{1}[ \cdot\geq b_{i}]\right\|_{L_{2}(P)}^{2} \leq\frac{\|\mu\|_{1}^{2}\sup_{b\in[0,1]}\|\mathbf{1}[\cdot\geq b ]\|_{L_{2}(P)}^{2}}{k}$$ $$=\frac{1}{k}\left(\int_{0}^{1}|f^{\prime}(b)|\mathrm{d}b\right)^{ 2}.$$
2. Now consider the Fourier representation via Barron's theorem: $$f(x)-f(0) =-2\pi\iint_{0}^{\|w\|}\mathbf{1}[w^{\mathsf{T}}x-b\geq 0] \left[\sin(2\pi b+2\pi\theta(w))|\hat{f}(w)|\right]\mathrm{d}b\mathrm{d}w$$ $$\quad+2\pi\iint_{-\|w\|}^{0}\mathbf{1}[-w^{\mathsf{T}}x+b\geq 0] \left[\sin(2\pi b+2\pi\theta(w))|\hat{f}(w)|\right]\mathrm{d}b\mathrm{d}w,$$ and also our calculation that the corresponding measure \(\mu\) on thresholds has \(\|\mu\|_{1}\leq 2\|\widehat{\nabla f}(w)\|\). Then Maurey's lemma implies that there exist \(((w_{i},b_{i},s_{i}))_{i=1}^{m}\) such that, for any probability measure \(P\) support on \(\|x\|\leq 1\), $$\left\|f(\cdot)-f(0)-\frac{\|\mu\|_{1}}{k}\sum_{i}s_{i}\mathbf{1} [\langle w_{i},\cdot\rangle\geq b_{i}]\right\|_{L_{2}(P)}^{2} \leq\frac{\|\mu\|_{1}^{2}\sup_{w,b}\|\mathbf{1}[\langle w,\cdot \rangle\geq b]\|_{L_{2}(P)}^{2}}{k}$$ $$\leq\frac{4\|\widehat{\nabla f}(w)\|^{2}}{k}.$$
In this section we consider networks close to their random initialization. Briefly, the core idea is to compare a network \(f:\mathbb{R}^{d}\times\mathbb{R}^{p}\to\mathbb{R}\), which takes input \(x\in\mathbb{R}^{d}\) and has parameters \(W\in\mathbb{R}^{p}\), to its first-order Taylor approximation at random initialization \(W_{0}\):

$$f_{0}(x;W):=f(x;W_{0})+\left\langle\nabla f(x;W_{0}),W-W_{0}\right\rangle.$$

The key property of this simplification is that while it is nonlinear in \(x\), it is affine in \(W\), which will greatly ease analysis. This section is roughly organized as follows

* 4.1 gives the basic setup in more detail, including the networks considered and the specific random initialization. The study is almost solely on shallow networks, since the deep case currently only leads to a degraded analysis and is not well understood.
* 4.2 shows that near initialization, with large width, \(f\approx f_{0}\).
* 4.3 provides the "kernel view": since the previous part shows we are effectively linear over some feature space, it is natural to consider the kernel corresponding to that feature space. This provides many connections to the literature (via "neural tangent kernel" (NTK)), and also is used for a short proof that these functions near initialization are already universal approximators!

### Basic setup: Taylor expansion of shallow networks

As explained shortly, we will almost solely consider the shallow case:

$$f(x;W):=\frac{1}{\sqrt{m}}\sum_{j=1}^{m}a_{j}\sigma(w_{j}^{\intercal}x),\qquad W :=\begin{bmatrix}\gets w_{1}^{\intercal}\to\\ \vdots\\ \gets w_{m}^{\intercal}\to\end{bmatrix}\in\mathbb{R}^{m\times d}, \tag{2}$$

where \(\sigma\) will either be a smooth activation or the ReLU, and we will treat \(a\in\mathbb{R}^{m}\) as fixed and only allow \(W\in\mathbb{R}^{m\times d}\) to vary. There are a number of reasons for this exact formalism, they are summarized below in Remark 4.1.

Now let's consider the corresponding first-order Taylor approximation \(f_{0}\) in detail. Consider any univariate activation \(\sigma\) which is differentiable except on a set of measure zero (e.g., countably many points), and Gaussian initialization \(W_{0}\in\mathbb{R}^{m\times d}\) as before. Consider the Taylor expansion at initialization:

$$f_{0}(x;W) =f(x;W_{0})+\left\langle\nabla f(x;W_{0}),W-W_{0}\right\rangle$$ $$=\frac{1}{\sqrt{m}}\sum_{j=1}^{m}a_{j}\left(\sigma(w_{0,j}^{ \intercal}x)+\sigma^{\prime}(w_{0,j})x^{\intercal}(w_{j}-w_{0,j})\right)$$ $$=\frac{1}{\sqrt{m}}\sum_{j=1}^{m}a_{j}\left(\left[\sigma(w_{0,j}^ {\intercal}x)-\sigma^{\prime}(w_{0,j})w_{0,j}^{\intercal}x\right]+\sigma^{ \prime}(w_{0,j})w_{j}^{\intercal}x\right).$$

If \(\sigma\) is nonlinear, then this mapping is nonlinear in \(x\), despite being affine in \(W!\) Indeed \(\nabla f(\cdot;W_{0})\) defines a feature mapping:

$$\nabla f(x;W_{0}):=\begin{bmatrix}\gets&a_{1}\sigma^{\prime}(w_{0,1}^{ \intercal}x)x^{\intercal}&\to\\ &\vdots&\\ \gets&a_{m}\sigma^{\prime}(w_{0,m}^{\intercal}x)x^{\intercal}&\to\end{bmatrix};$$the predictor \(f_{0}\) is affine is an affine function of the parameters, and is also affine in this feature-mapped data.

**Remark 4.1** (rationale for eq. 2): _The factor \(\frac{1}{\sqrt{m}}\) will make the most sense in 4.3, it gives a normalization that leads to a kernel. We only vary the inner layer \(W\) and keep the outer layer \(a\) fixed to have a nontrivial (nonlinear) model which still leads to non-convex training, but is arguably the simplest such. Random initialization is classical and used for many reasons, a classical one being a "symmetry break" which makes nodes distinct and helps with training [16]. A standard initialization, is to have the first layer Gaussian with standard deviation \(1/\sqrt{d}\), and the second layer Gaussian with standard deviation \(1/\sqrt{m}\); in the case of the ReLU, positive constants can be pulled through, and equivalently we can use standard Gaussian initialization and place a coefficient \(1/\sqrt{md}\) out front; here we drop the \(1/\sqrt{d}\) since we want to highlight a behavior that varies with \(m\), whereas \(1/\sqrt{d}\) is a constant. To simplify further, we will make the second layer \(\pm 1\). pytorch initialization defaults to these standard deviations, but defaults to uniform distributions and not Gaussians. Lastly, some papers managed to set up analysis so that the final layer does most of the work (and the training problem is convex for the last layer), thus we follow the convention of some authors to train all but the last layer to rule out this possibility._

**Remark 4.2**: _Many researchers use the term "overparameterization" to refer to a number of phenomena, but rooted at their core in the use of many more parameters than are seemingly necessary. E.g., we know from the earlier sections that some number of nodes suffice to approximate certain types of functions, but in this section we see we might as well take the width \(m\) arbitrarily large. Mainly classical perspectives on the behavior of networks (e.g., their generalization properties) worsen with large width, so "overparameterization" also highlights many of these apparent contradictions._

**Remark 4.3** (main bibliography for NTK): _The paper that made the term "NTK" is [17], which also argued gradient descent follows the NTK; a kernel connection was observed earlier in [18]._

Another very influential work is [10], which showed that one can achieve arbitrarily small training error by running gradient descent on a large-width network, which thus stays within the NTK regime (close to initialization).

A few other early optimization references are [19] (Arora, Du, Hu, Li, and Wang 2019) (Allen-Zhu, Li, and Liang 2018). Also nearly parallel with [17, 19] were [18, 19].

Estimates of empirical infinite width performance are in [1] and [20].

**(Various further works.): _The NTK has appeared in a vast number of papers (and various papers use linearization and study the early stage of training, whether they refer to it as the NTK or not). Concurrent works giving general convergence to global minima are [19, 10, 11, 12]. Many works subsequently aimed to reduce the width dependence [19, 19]; in the classification case, a vastly smaller width is possible [18, 19]. Another subsequent direction (in the regression case) was obtaining test error and not just training error bounds [19, 17, 18]. Lastly, another interesting point is the use of noisy gradient desceent in some of these analyses (Allen-Zhu, Li, and Liang 2018; Z. Chen et al. 2020). Some works use the term \(F_{2}\) to refer to the kernel space we get after taking a Taylor expansion, and also constrast this with the space \(F_{1}\) we get byu considering all possible neural networks (e.g., those that are a discrete sum of nodes, which can not be represented exactly with a finite-norm element of the RKHS \(F_{2}\)); this term mostly appears in papers with Francis Bach, see for instance Chizat and Bach (2020).

**Remark 4.4**: _(scaling and temperature)_: Some authors including a multiplicative factor \(\epsilon>0\) on the network output, meaning

$$\frac{\epsilon}{\sqrt{m}}\sum_{j=1}^{m}a_{j}\sigma(w_{j}^{\mathsf{T}}x).$$

Considering the effect of introducing \(\epsilon\) in \(f_{0}\) as well, one can interpret this as having two effects:

* Scaling down the initial random predictions \(f(x;W_{0})=f_{0}(x;W_{0})\). These initial predictions are random and, without \(\epsilon>0\), are of order \(\mathcal{O}(1)\); it therefore takes gradient descent quite a bit of work just to zero out this initial random noise. All together, papers, deal with this random noise in effectively four ways: 1. using \(\epsilon>0\) as described here, 2. using "symmetric" initialization which forces \(f(x;W_{0})=0\) in various ways, 3. simply running more gradient descent to clear the noise, which in turn may require larger width, 4. considering the well-separated classification setting, which does not need to fully clear the noise, but rather just "push it to one side."
* Scaling down the gradient. As such, many works which do not have \(\epsilon>0\) instead use a small step size, e.g., \(1/\sqrt{m}\).

Some authors fix \(\epsilon\) as a function of \(m\) and consider a resulting "scaling" behavior, namely that by taking \(m\to 0\), the Taylor expansion "zooms in," and this provides one explanation of the behavior of the NTK; this perspective was summarized in (Chizat and Bach 2019).

**Remark 4.5**: _(Practical regimes)_: "NTK regime" or "near initialization" are not well-defined, though generally the proofs in this setup require some combination of \(\|W-W_{0}\|_{\mathrm{F}}=\mathcal{O}(1)\) (or the stronger form \(\max_{j}\|\mathbf{e}_{j}^{\mathsf{T}}(W-W_{0})\|_{2}=\mathcal{O}(1/\sqrt{m})\)), and/or at most \(1/\sqrt{m}\) fraction of the activations change. In practice, these all seem to be violated almost immediately (e.g., just one or two steps of gradient descent), but still the idea captures many interesting phenomena near initialization and do not degrade with overparameterization as do other approaches.

**Remark 4.6**: _(multi-layer case)_: Let \(\vec{W}=(W_{L},\ldots,W_{1})\) denote a tuple of the parameters for each layer, whereby the Taylor expansion at initial values \(\vec{W}_{0}\) now becomes

$$x\mapsto f(x;\vec{W})+\left\langle\vec{W}-\vec{W}_{0},\nabla f(x;\vec{W}_{0}) \right\rangle.$$

The inner product with \(\nabla f(x;\vec{W}_{0})\) decomposes over layers, giving

$$\left\langle\vec{W}-\vec{W}_{0},\nabla f(x;\vec{W}_{0})\right\rangle=\sum_{k= 1}^{L}\left\langle W_{k}-W_{0,k},\nabla_{W_{k}}f(x;\vec{W}_{0})\right\rangle.$$

We will revisit this multi-layer form later when discussing kernels.

**Remark 4.7**: _(Taylor expansion around \(0\))_: There are a few reasons why we do the Taylor expansion around initialization; the main one is that Taylor approximation improves the closer you get to the point you are approximating, another one is that bounds that scale with \(\|W\|_{\mathrm{F}}\) can be re-centered to now scale with the potentially much smaller quantity \(\|W-W_{0}\|_{\mathrm{F}}\), and lastly we get to invoke Gaussian concentration tools. Note however how things completely break down if we do what might initially seem a reasonable alternative: Taylor expansion around \(0\). Then we get

$$f(x;0)+\langle\nabla f(x;0),W-0\rangle=\frac{1}{\sqrt{m}}\sum_{j=1}^{m}a_{j} \left(\sigma(0)+\sigma^{\prime}(0)x^{\mathrm{ T}}w_{j}\right).$$

This is once again affine in the parameters, but it is also affine in the inputs! So we don't have any of the usual power of neural networks.

**Remark 4.8**: _(simplification with the ReLU)_: If we use the ReLU \(\sigma(z)=\max\{0,z\}\), then the property \(\sigma(z)=z\sigma^{\prime}(z)\) (which is fine even at \(0\)!) means

$$\sigma(w_{0,j}^{\mathrm{ T}}x)-\sigma^{\prime}(w_{0,j}^{\mathrm{ T}}x)w_{0,j}^{\mathrm{ T}}x=0,$$

and thus \(f_{0}\) as above simplifies to give

$$f_{0}(x;W) =\frac{1}{\sqrt{m}}\sum_{j=1}^{m}a_{j}\left(\left[\sigma(w_{0,j} ^{\mathrm{ T}}x)-\sigma^{\prime}(w_{0,j})w_{0,j}^{\mathrm{ T}}x\right]+\sigma^{ \prime}(w_{0,j})w_{j}^{\mathrm{ T}}x\right)$$ $$=\frac{1}{\sqrt{m}}\sum_{j=1}^{m}a_{j}\sigma^{\prime}(w_{0,j})w_{ j}^{\mathrm{ T}}x=\langle\nabla f(x;W_{0}),W\rangle\,.$$

### Networks near initialization are almost linear

Our first step is to show that \(f-f_{0}\)_shrinks_ as \(m\) increases, which has a few immediate consequences.

* It gives one benefit of "overparameterization."
* It gives us an effective way to do universal approximation with small \(\|W-W_{0}\|\): we simply make \(m\) as large as needed and get more functions inside our RKHS.

First we handle the case that \(\sigma\) is smooth, by which we mean \(\sigma^{\prime\prime}\) exists and satisfies \(|\sigma^{\prime\prime}|\leq\beta\) everywhere. This is not satisfied for the ReLU, but the proof is so simple that it is a good motivator for other cases.

**Proposition 4.1**: If \(\sigma:\mathbb{R}\to\mathbb{R}\) is \(\beta\)-smooth, and \(|a_{j}|\leq 1\), and \(\|x\|_{2}\leq 1\), then for any parameters \(W,V\in\mathbb{R}^{m\times d}\),

$$|f(x;W)-f_{0}(x;V)|\leq\frac{\beta}{2\sqrt{m}}\left\|W-V\right\|_{\mathrm{F}}^ {2}.$$

**Proof.** By Taylor's theorem,

$$\left|\sigma(r)-\sigma(s)-\sigma^{\prime}(s)(r-s)\right|=\left|\int_{r}^{s} \sigma^{\prime\prime}(z)(s-z)\mathrm{d}z\right|\leq\frac{\beta(r-s)^{2}}{2}.$$Therefore

$$|f(x;W)-f(x;V)-\langle\nabla f(x;V),W-V\rangle|$$ $$\leq\frac{1}{\sqrt{m}}\sum_{j=1}^{m}|a_{j}|\cdot\left|\sigma(w_{j}^ {\mathsf{T}}x)-\sigma(v_{j}^{\mathsf{T}}x)-\sigma^{\prime}(v_{j}^{\mathsf{T}}x) x^{\mathsf{T}}(w_{j}-v_{j})\right|$$ $$\leq\frac{1}{\sqrt{m}}\sum_{j=1}^{m}\frac{\beta(w_{j}^{\mathsf{T} }x-v_{j}^{\mathsf{T}}x)^{2}}{2}$$ $$\leq\frac{\beta}{2\sqrt{m}}\sum_{j=1}^{m}\|w_{j}-v_{j}\|^{2}$$ $$=\frac{\beta}{2\sqrt{m}}\left\|W-V\right\|_{\mathrm{F}}^{2}.$$

**Remark 4.9**: The preceding lemma holds for any \(W\), and doesn't even need the Gaussian structure of \(W_{0}\). This is unique to this shallow case, however; producing an analogous inequality with multiple layers of smooth activations will need to use random initialization.

Now we switch to the ReLU. The proof is much more complicated, but is instructive of the general calculations one must perform frequently with the ReLU.

**Remark 4.10**: A multi-layer version of the following originally appeared in [1]; there, the multiple layers only _hurt_ the bound, introducing factors based on depth. Moreover, the proof is much more complicated. Due to this, we only use a straightforward single-layer version, which appeared later in [11].
**Lemma 4.1**: For any radius \(B\geq 0\), for any fixed \(x\in\mathbb{R}^{d}\) with \(\|x\|\leq 1\), with probability at least \(1-\delta\) over the draw of \(W_{0}\), for any \(W\in\mathbb{R}^{m\times d}\) with \(\|W-W_{0}\|_{\mathrm{F}}\leq B\),

$$|f(x;W)-f_{0}(x;W)|\leq\frac{2B^{4/3}+B\ln(1/\delta)^{1/4}}{m^{1/6}},$$

and given any additional \(V\in\mathbb{R}^{m\times d}\) with \(\|V-W_{0}\|_{\mathrm{F}}\leq B\),

$$|f(x;V)-(f(x;W)+\langle\nabla_{W}f(x;W),V-W\rangle)|\leq\frac{6B^{4/3}+2B\ln(1 /\delta)^{1/4}}{m^{1/6}}.$$

**Remark 4.11**: _(incorrect approach)_: Let's see how badly things go awry if we try to brute-force the proof. By similar reasoning to the earlier ReLU simplification,

$$|f(x;W)-f_{0}(x;W)| =|\langle\nabla f(x;W),W\rangle-\langle\nabla f(x;W_{0}),W\rangle|$$ $$=\left|\frac{1}{\sqrt{m}}\sum_{j}a_{j}\left(\mathbf{1}[w_{j}^{ \mathsf{T}}x\geq 0]-\mathbf{1}[w_{0,j}^{\mathsf{T}}x\geq 0\right)w_{j}^{ \mathsf{T}}x\right|.$$

A direct brute-forcing with no sensitivity to random initialization gives

$$|f(x;W)-f_{0}(x;W)|\leq\frac{1}{\sqrt{m}}\sum_{j}\|w_{j}\|\leq\|W\|_{\mathrm{F}}.$$

We can try to save a bit by using the randomness of \((a_{j})_{j=1}^{m}\), but since Lemma 4.1 is claimed to hold for every \(\|W-W_{0}\|_{\mathrm{F}}\leq B\), the argument might be complicated. Our eventual proof will only use randomness of \(W_{0}\).

The proof will use the following concentration inequality.

**Lemma 4.2**: For any \(\tau>0\) and \(x\in\mathbb{R}^{d}\) with \(\|x\|>0\), with probability at least \(1-\delta\),

$$\sum_{j=1}^{m}\mathbf{1}\left[|w_{j}^{\mathsf{ T}}x|\leq\tau\|x\|\right]\leq m\tau+\sqrt{\frac{m}{2}\ln\frac{1}{\delta}}.$$

**Proof.** For any row \(j\), define an indicator random variable

$$P_{j}:=\mathbf{1}[|w_{j}^{\mathsf{ T}}x|\leq\tau\|x\|].$$

By rotational invariance, \(P_{j}=\mathbf{1}[|w_{j,1}|\leq\tau]\), which by the form of the Gaussian density gives

$$\Pr[P_{j}=1]=\int_{-\tau}^{+\tau}\frac{1}{\sqrt{2\pi}}e^{-z^{2}/2}\mathrm{d}z \leq\frac{2\tau}{\sqrt{2\pi}}\leq\tau.$$

By Hoeffding's inequality, with probability at least \(1-\delta\),

$$\sum_{j=1}^{m}P_{j}\leq m\Pr[P_{1}=1]+\sqrt{\frac{m}{2}\ln\frac{1}{\delta}}\leq m \tau+\sqrt{\frac{m}{2}\ln\frac{1}{\delta}}.$$

**Proof of Lemma 4.1.** Fix \(x\in\mathbb{R}^{d}\). If \(\|x\|=0\), then for any \(W\in\mathbb{R}^{d}\), \(f(x;W)=0=f_{0}(x;W)\), and the proof is complete; henceforth consider the case \(\|x\|>0\).

The proof idea is roughly as follows. The Gaussian initialization on \(W_{0}\) concentrates around a rather large shell, and this implies \(|w_{0,j}^{\mathsf{ T}}x|\) is large with reasonably high probability. If \(\|W-W_{0}\|_{\mathrm{F}}\) is not too large, then \(\|w_{j}-w_{0,j}\|\) must be small for most coordinates; this means that \(w_{j}^{\mathsf{ T}}x\) and \(w_{0,j}^{\mathsf{ T}}x\) must have the same sign for most \(j\).

Proceeding in detail, fix a parameter \(r>0\), which will be optimized shortly. Let \(W\) be given with \(\|W-W_{0}\|\leq B\). Define the sets

$$S_{1} :=\left\{j\in[m]:|w_{j}^{\mathsf{ T}}x|\leq r\|x\|\right\},$$ $$S_{2} :=\left\{j\in[m]:\|w_{j}-w_{0,j}\|\geq r\right\},$$ $$S :=S_{1}\cup S_{2}.$$

By Lemma 4.2, with probability at least \(1-\delta\),

$$|S_{1}|\leq rm+\sqrt{m\ln(1/\delta)}.$$

On the other hand,

$$B^{2}\geq\|W-W_{0}\|^{2}\geq\sum_{j\in S_{2}}\|w_{j}-w_{0,j}\|^{2}\geq|S_{2}|r ^{2},$$

meaning \(|S_{2}|\leq B^{2}/r^{2}\). For any \(j\not\in S\), if \(w_{j}^{\mathsf{ T}}x>0\), then

$$w_{0,j}^{\mathsf{ T}}x\geq w_{j}^{\mathsf{ T}}x-\|w_{j}-w_{0,j}\|\cdot\|x\|>\|x\|\,(r-r)=0,$$

meaning \(\mathbf{1}[w_{j}^{\mathsf{ T}}x\geq 0]=\mathbf{1}[w_{0,j}^{\mathsf{ T}}x\geq 0]\); the case that \(j\not\in S\) and \(w_{j}^{\mathsf{ T}}x<0\) is analogous. Together,

$$|S|\leq rm+\sqrt{m\ln(1/\delta)}+\frac{B^{2}}{r^{2}}\quad\text{and}\quad j \not\in S\Longrightarrow\mathbf{1}[w_{j}^{\mathsf{ T}}x\geq 0]=\mathbf{1}[w_{0,j}^{\mathsf{ T}}x\geq 0].$$Lastly, we can finally choose \(r\) to balance terms in \(|S|\): picking \(r:=B^{2/3}/m^{1/3}\) gives

$$|S|\leq(Bm)^{2/3}+\sqrt{m\ln(1/\delta)}+(Bm)^{2/3}\leq m^{2/3}\left(2B^{2/3}+ \sqrt{\ln(1/\delta)}\right).$$

Now that \(|S|\) has been bounded, the proof considers the two different statements separately, though their proofs are similar.

1. As in the above remark, $$|f(x;W)-f_{0}(x;W)| =|\langle\nabla f(x;W)-\nabla f(x;W_{0}),W\rangle|$$ $$=\frac{1}{\sqrt{m}}\left|\sum_{j}a_{j}\left(\mathbf{1}[w_{j}^{ \intercal}x\geq 0]-\mathbf{1}[w_{0,j}^{\intercal}x\geq 0]\right)w_{j}^{\intercal}x\right|$$ $$\leq\frac{1}{\sqrt{m}}\sum_{j}\left|\mathbf{1}[w_{j}^{\intercal} x\geq 0]-\mathbf{1}[w_{0,j}^{\intercal}x\geq 0]\right|\cdot|w_{j}^{\intercal}x|.$$ To simplify this, as above \(\left|\mathbf{1}[w_{j}^{\intercal}x\geq 0]-\mathbf{1}[w_{0,j}^{\intercal}x\geq 0 ]\right|\) is only nonzero for \(j\in S\). But when it is nonzero, this means \(\text{sgn}(w_{j}^{\intercal}x)\neq\text{sgn}(w_{0,j}^{\intercal}x)\), and thus \(|w_{j}^{\intercal}x|\leq|w_{j}^{\intercal}x-w_{0,j}^{\intercal}x|\), and together with Cauchy-Schwarz (two applications!), and the above upper bound on \(|S|\) gives $$|f(x;W)-f_{0}(x;W)| \leq\frac{1}{\sqrt{m}}\sum_{j}\left|\mathbf{1}[w_{j}^{\intercal}x \geq 0]-\mathbf{1}[w_{0,j}^{\intercal}x\geq 0]\right|\cdot|w_{j}^{\intercal}x|$$ $$\leq\frac{1}{\sqrt{m}}\sum_{j\in S}\left|w_{j}^{\intercal}x-w_{0, j}^{\intercal}x\right|$$ $$\leq\frac{1}{\sqrt{m}}\sum_{j\in S}\left\|w_{j}-w_{0,j}\right\|$$ $$\leq\frac{1}{\sqrt{m}}\sqrt{|S|}\cdot\|W-W_{0}\|_{\text{F}}$$ $$\leq B\sqrt{\frac{|S|}{m}}$$ $$\leq B\sqrt{\frac{2B^{2/3}+\sqrt{\ln(1/\delta)}}{m^{1/3}}}$$ $$\leq\frac{2B^{4/3}+B\ln(1/\delta)^{1/4}}{m^{1/6}}.$$
2. Following similar reasoning, $$|f(x;V)-(f(x;W)+\langle\nabla_{W}f(x;W),V-W\rangle)|$$ $$=|\langle\nabla f(x;V)-\nabla f(x;W),V\rangle|$$ $$=\frac{1}{\sqrt{m}}\left|\sum_{j}a_{j}\left(\mathbf{1}[w_{j}^{ \intercal}x\geq 0]-\mathbf{1}[v_{j}^{\intercal}x\geq 0]\right)v_{j}^{ \intercal}x\right|$$ $$\leq\frac{1}{\sqrt{m}}\left|\sum_{j}a_{j}\left(\mathbf{1}[w_{j}^ {\intercal}x\geq 0]-\mathbf{1}[v_{j}^{\intercal}x\geq 0]\right)\right|\cdot \left|w_{j}^{\intercal}x-v_{j}^{\intercal}x\right|$$ $$\leq\frac{1}{\sqrt{m}}\left|\sum_{j}a_{j}\left(\mathbf{1}[w_{j}^ {\intercal}x\geq 0]-\mathbf{1}[v_{j}^{\intercal}x\geq 0]\right)\right|\cdot \left\|w_{j}-v_{j}\right\|.$$Now define \(S_{3}\) analogously to \(S_{2}\), but for the new matrix \(V\):

$$S_{3}:=\left\{j\in[m]:\|v_{j}-w_{0,j}\|\geq r\right\},$$

and additionally define

$$S_{4}:=S_{1}\cup S_{2}\cup S_{3}.$$

By the earlier choice of \(r\) and related calculations, with probability at least \(1-\delta\),

$$|S|\leq rm+\sqrt{m\ln(1/\delta)}+\frac{2B^{2}}{r^{2}}\leq m^{2/3}\left(3B^{2/3 }+\sqrt{\ln(1/\delta)}\right).$$

Plugging this back in and continuing as before,

$$|\langle\nabla f(x;V)-\nabla f(x;W),V\rangle| \leq\frac{1}{\sqrt{m}}\left|\sum_{j}a_{j}\left(\mathbf{1}[w_{j}^ {\mathsf{T}}x\geq 0]-\mathbf{1}[v_{j}^{\mathsf{T}}x\geq 0]\right)\right|\cdot\|w_{j }-v_{j}\|.$$ $$\leq\frac{1}{\sqrt{m}}\sum_{j\in S_{4}}\|w_{j}-v_{j}\|_{\mathrm{F}}$$ $$\leq\frac{1}{\sqrt{m}}\sqrt{|S_{4}|}\|V-W\|_{\mathrm{F}}$$ $$\leq 2B\sqrt{\frac{3B^{2/3}+\sqrt{\ln(1/\delta)}}{m^{1/3}}}$$ $$\leq\frac{6B^{4/3}+2B\ln(1/\delta)^{1/4}}{m^{1/6}}.$$

### Properties of the kernel at initialization

So far, we've said that \(f-f_{0}\) is small when the width is large. Now we will focus on \(f_{0}\), showing that it is a large class of functions; thus, when the width is large, \(f\) obtained with small \(\|W-W_{0}\|_{\mathrm{F}}\) can also capture many functions.

**Remark 4.12** (kernel view): This analysis will take the kernel/RKHS view of \(f_{0}\). The amount that this perspective appears varies by treatments near initialization, including papers which never explicitly use any kernel concepts. In the original paper giving the name "NTK" (Jacot, Gabriel, and Hongler 2018), only \(f_{0}\) (and not \(f\)) was considered, indeed in the multi-layer case, and in the infinite-width case, using a Gaussian process with a kernel given as here. We won't use this perspective here.

To start, let us see how to define a kernel. In the standard kernel setup, the kernel can be written as the inner product between feature mappings for two data points:

$$k_{m}(x,x^{\prime}) :=\left\langle\nabla f(x;W_{0}),\nabla f(x^{\prime};W_{0})\right\rangle$$ $$=\left\langle\begin{bmatrix}\longleftarrow&a_{1}x^{\mathsf{T}} \sigma^{\prime}(w_{1,0}^{\mathsf{T}}x)/\sqrt{m}&\longrightarrow\\ &\vdots&\\ \longleftarrow&a_{m}x^{\mathsf{T}}\sigma^{\prime}(w_{m,0}^{\mathsf{T}}x)/\sqrt {m}&\longrightarrow\end{bmatrix},\begin{bmatrix}\longleftarrow&a_{1}(x^{ \prime})^{\mathsf{T}}\sigma^{\prime}(w_{1,0}^{\mathsf{T}}x^{\prime})/\sqrt{m}& \longrightarrow\\ &\vdots&\\ \longleftarrow&a_{m}(x^{\prime})^{\mathsf{T}}\sigma^{\prime}(w_{m,0}^{ \mathsf{T}}x^{\prime})/\sqrt{m}&\longrightarrow\end{bmatrix}\right\rangle$$ $$=\frac{1}{m}\sum_{j=1}^{m}a_{j}^{2}\left\langle x\sigma^{\prime}( w_{j,0}^{\mathsf{T}}x),x^{\prime}\sigma^{\prime}(w_{j,0}^{\mathsf{T}}x^{ \prime})\right\rangle$$ $$=x^{\mathsf{T}}x^{\prime}\left[\frac{1}{m}\sum_{j=1}^{m}\sigma^{ \prime}(w_{j,0}^{\mathsf{T}}x)\sigma^{\prime}(w_{j,0}^{\mathsf{T}}x^{\prime}) \right].$$

This gives one justification of the \(1/\sqrt{m}\) factor: now this kernel is an average and not a sum, and we should expect it to have a limit as \(m\to\infty\). To this end, and noting that the rows \((w_{0,j}^{\mathsf{T}})_{j=1}^{m}\) are iid, then each term of the summation is iid, so by the SLLN, almost surely

$$k_{m}(x,x^{\prime})\xrightarrow{m\to\infty}k(x,x^{\prime}):=x^{\mathsf{T}}x^{ \prime}\mathop{\mathbb{E}}_{w}\left[\sigma^{\prime}(w^{\mathsf{T}}x)\sigma^{ \prime}(w^{\mathsf{T}}x^{\prime})\right].$$

In homework we will (a) provide a more explicit form as _dot product kernel_, and (b) bound the difference exactly. [ mjt(r): add explicit ref.]

For now, let us calculate the closed form for the ReLU; let's do this geometrically. [ mjt(r): need to include picture proof]

* Consider the plane spanned by \(x\) and \(x^{\prime}\). Since projections of standard Gaussians are again standard Gaussians, we can consider a Gaussian random vector \(v\in\mathbb{R}^{2}\) in this plane.
* The integrand in the expectation is \(1\) iff \(v^{\mathsf{T}}x\geq 0\) and \(v^{\mathsf{T}}x^{\prime}\geq 0\). Since \(\|v\|\) does not affect these expressions, we can simplify \(v\in\mathbb{R}^{2}\) further to be sampled uniformly from the surface of the sphere.
* Suppose \(\|x\|=1=\|x^{\prime}\|\), and define \(\theta:=\arccos{(x^{\mathsf{T}}x^{\prime})}\); then the integrand is \(1\) if \(v\) has positive inner product with both \(x\) and \(x^{\prime}\), which has probability $$\frac{\pi-\theta}{2\pi}.$$

Together, still using \(\|x\|=1=\|x^{\prime}\|\),

$$k(x,x^{\prime})=x^{\mathsf{T}}x^{\prime}\mathop{\mathbb{E}}_{w}1[w^{\mathsf{T }}x\geq 0]\cdot\mathbf{1}[w^{\mathsf{T}}x^{\prime}\geq 0]=x^{\mathsf{T}}x^{ \prime}\left(\frac{\pi-\arccos(x^{\mathsf{T}}x^{\prime})}{2\pi}\right).$$

**Remark 4.13**: _(multi-layer kernel)_: Let's revisit the multi-layer case, and develop the multi-layer kernel. Suppose the width of every layer except the final one is \(m\), specifically \(W_{1}\in\mathbb{R}^{m\times d}\), and \(W_{L}\in\mathbb{R}^{1\times m}\), and otherwise \(W_{i}\in\mathbb{R}^{m\times m}\). Then the kernel also decomposes over layers, giving

$$\tilde{k}_{m}(x,x^{\prime}) :=\left\langle\nabla f(x;\vec{W}_{0}),\nabla f(x^{\prime};\vec{W}_ {0})\right\rangle$$ $$:=\sum_{i=1}^{L}\left\langle\nabla_{W_{i}}f(x;\vec{W}_{0}),\nabla _{W_{i}}f(x^{\prime};\vec{W}_{0})\right\rangle.$$It is not clear how powerful this representation is, and if it is fundamentally more powerful than the single-layer version. On the one hand, it decomposes over layers and is thus a sum (and not composition) of kernels; on the other hand, each layer does work with the forward mapping of previous layers. There is some work on this topic, though it is far from closing the question (Bietti and Bach 2020); meanwhile, the linearization inequalities in section 4.2 seemingly degrade with depth, so the tradeoffs could be intricate, and also could put serious question on how much the early phase near initialization is relevant in practice.

**Remark 4.14**: _(kernel of Taylor expansion at \(0\))_Let's also revisit the Taylor expansion at \(0\), but now with kernels. Before, we noted that the feature expansion is _linear_, rather than non-linear, in the data:

$$\nabla f(x;0)=\begin{bmatrix}\leftarrow&a_{1}\sigma^{\prime}(0)x^{\mathrm{ T}}/\sqrt{m}&\rightarrow\\ &\vdots&\\ \leftarrow&a_{m}\sigma^{\prime}(0)x^{\mathrm{ T}}/\sqrt{m}&\rightarrow\end{bmatrix}=\frac{\sigma^{\prime}(0)}{\sqrt{m}} \begin{bmatrix}\leftarrow&a_{1}x^{\mathrm{ T}}&\rightarrow\\ &\vdots&\\ \leftarrow&a_{m}x^{\mathrm{ T}}&\rightarrow\end{bmatrix};$$

as mentioned before, this is in contrast to the Taylor expansion at initialization, which is nonlinear in the data. Moreover, the corresponding kernel is a rescaling of the linear kernel:

$$\langle\nabla f(x;0),\nabla f(x^{\prime};0)\rangle =\frac{\sigma^{\prime}(0)^{2}}{m}\left\langle\begin{bmatrix} \leftarrow&a_{1}x^{\mathrm{ T}}&\rightarrow\\ &\vdots&\\ \leftarrow&a_{m}x^{\mathrm{ T}}&\rightarrow\end{bmatrix},\begin{bmatrix} \leftarrow&a_{1}(x^{\prime})^{\mathrm{ T}}&\rightarrow\\ &\vdots&\\ \leftarrow&a_{m}(x^{\prime})^{\mathrm{ T}}&\rightarrow\end{bmatrix}\right\rangle$$ $$=\frac{\sigma^{\prime}(0)^{2}}{m}\sum_{j=1}^{m}a_{j}^{2}x^{ \mathrm{ T}}x^{\prime}=\sigma^{\prime}(0)^{2}x^{\mathrm{ T}}x^{\prime}.$$

Now let's return to the task of assessing how many functions we can represent near initialization. For this part, we will fix one degree of freedom in the data to effectively include a bias term; this is not necessary, but gives a shorter proof by reducing to standard kernel approximation theorems. We will show that this class is a universal approximator. Moreover \(\|W-V\|\) will correspond to the RKHS norm, thus by making the width large, we can approximate elements of this large RKHS arbitrarily finely.

Proceeding in detail, first let's define our domain

$$\mathcal{X}:=\left\{x\in\mathbb{R}^{d}:\|x\|=1,x_{d}=1/\sqrt{2}\right\},$$

and our predictors

$$\mathcal{H}:=\left\{x\mapsto\sum_{j=1}^{m}\alpha_{j}k(x,x_{j})\ :\ m\geq 0, \alpha_{j}\in\mathbb{R},x_{j}\in\mathcal{X}\right\}.$$

This might look fancy, but is the same as the functions we get by starting with \(x\mapsto\langle\nabla f(x;W_{0}),W-W_{0}\rangle\) and allowing the width to go to infinity, and \(\|W-W_{0}\|\) be arbitrarily large; by the results in section 4.2, we can always choose an arbitrarily large width so that \(f-f_{0}\approx 0\) even when \(\|W-W_{0}\|\) is large, and we will also show that large width approximates infinite width in the homework. As such, it suffices to show that \(\mathcal{H}\) is a universal approximator over \(\mathcal{X}\).

**Theorem 4.1**: \(\mathcal{H}\) _is a universal approximator over \(\mathcal{X}\); that is to say, for every continuous \(g:\mathbb{R}^{d}\rightarrow\mathbb{R}\) and every \(\epsilon>0\), there exists \(h\in\mathcal{H}\) with \(\sup_{x\in\mathcal{X}}|g(x)-h(x)|\leq\epsilon\)._

**Remark 4.15**: The use of a bias is only to conveniently reduce to an existing result about kernels which are universal approximators. This result is stated over full-dimensional sets, and for this case the bias seems necessary. However, if we restrict to \(\|x\|=1\), the bias should not be necessary, though none of these automatic kernel theorems seem to apply (Notes to chapter 4, Steinwart and Christmann 2008).

**Proof.** Consider the set \(U:=\{u\in\mathbb{R}^{d-1}:\|u\|^{2}\leq 1/2\}\), and the kernel function

$$k(u,u^{\prime}):=f(u^{\mbox{\tiny T}}u^{\prime}),\qquad f(z):=\frac{(z+1/2)}{2 }-\frac{(z+1/2)\arccos(z+1/2)}{2\pi}.$$

We will show that this kernel is a universal approximator over \(U\), which means it is also a universal approximator on its boundary \(\{u\in\mathbb{R}^{d-1}:\|u\|^{2}=1/2\}\), and thus the kernel

$$(x,x^{\prime})\mapsto\frac{x^{\mbox{\tiny T}}x^{\prime}}{\pi}-\frac{x^{\mbox{ \tiny T}}x^{\prime}}{\arccos(x^{\mbox{\tiny T}}x^{\prime})}2\pi$$

is a universal approximator over \(\mathcal{X}\).

Going back to the original claim, first note that \(\arccos\) has the Maclaurin series

$$\arccos(z)=\frac{\pi}{2}-\sum_{k\geq 0}\frac{(2k)!}{2^{2k}(k!)^{2}}\left(\frac {z^{2k+1}}{2k+1}\right),$$

which is convergent for \(z\in[-1,+1]\). From here, it can be checked that \(f\) has a Maclaurin series where every term is not only nonzero, but positive (adding the bias ensured this). This suffices to ensure that \(k\) is a universal approximator (Corollary 4.57, Steinwart and Christmann 2008).

We have not quite closed the loop, as we have not combined the pieces to show that for any continuous function \(g\), we can select a large width \(m\) and \(W\) so that \(g\approx f_{0}(\cdot;W)\approx f(\cdot;W)\), but we've done most of the work, and a few remaining steps will be in homework. For a direct argument about this using a different approach based on (Barron 1993), see (Ji, Telgarsky, and Xian 2020).

## 5 Benefits of depth

So far we have given no compelling presentation of depth; in particular we have not justified the high depths used in practice.

In this section, we will give constructions of interesting functions by deep networks which can not be approximated by polynomially-sized shallow networks. These are only constructions, and it is unlikely these network structure are found by gradient descent and other practical methods, so the general question of justifying the high depth and particular architectures used in practice is still open.

There are four subsections to these notes.

1. First we will construct a simple piecewise-affine function, \(\Delta:\mathbb{R}\to\mathbb{R}\), which will be our building block of more complex behavior. When \(\Delta\) is composed with itself, it builds complexity exponentially fast in a variety of natural notions (e.g., exponentially many copies of itself).
2. Then we will show that \(\Delta^{L^{2}}\) can be easily written as a deep but constant width network,whereas a shallow network needs exponential width even for approximation within a constant.
3. Then we will use \(\Delta^{L}\) to approximate \(x^{2}\); this is meaningful because it leadsto many other approximations, and may seem more natural than \(\Delta^{L}\).
4. Lastly we will use \(x^{2}\) to approximate polynomials and Taylor expansions (Sobolev spaces).

**5.1**: **The humble \(\Delta\) mapping.**

Consider the \(\Delta\) function:

$$\Delta(x)=2\sigma_{\mathrm{r}}(x)-4\sigma_{\mathrm{r}}(x-1/2)+2\sigma_{\mathrm{ r}}(x-1)=\begin{cases}2x&x\in[0,1/2),\\ 2-2x&x\in[1/2,1),\\ 0&\text{otherwise.}\end{cases}$$

How does \(\Delta\) look? And how about \(\Delta^{2}:=\Delta\circ\Delta\)? And \(\Delta^{3}\)? [ mjt(r): Picture drawn in class; figures forthcoming.]

The pattern is that \(\Delta^{L}\) has \(2^{L-1}\) copies of it self, uniformly shrunk down. In a sense, complexity has increased exponentially as a function of the the number of nodes and layers (both \(\mathcal{O}(L)\)). Later, it will matter that we not only have many copies, but that they are identical (giving uniform spacing). For now, here's one way to characerize this behavior.

Let \(\langle x\rangle=x-\lfloor x\rfloor\) denote fractional part.

**Proposition 5.1**: Let \(\langle x\rangle:=x-\lfloor x\rfloor\) denote the fractional part of \(x\in\mathbb{R}\). Then

$$\Delta^{L}(x)=\Delta(\left\langle 2^{L-1}x\right\rangle)=\Delta(2^{L-1}x- \lfloor 2^{L-1}x\rfloor).$$

**Remark 5.1**: _(applications of \(\Delta\))_

* \(\Delta^{L}\) creates \(2^{L}\) (forward and backward) copies of its input, and thus is generally useful to replicate its input.
* Parity on the hypercube in dimension \(d=2^{L}\): \(\prod_{i=1}^{d}x_{i}=\Delta^{L-1}\left(\frac{d+\sum_{i}x_{i}}{2d}\right)\).
* We'll use \(\Delta\) when constructing \((x,y)\mapsto xy\).
* Digit extraction! (Which appears a lot in deep network lower and upper bounds!) (See also the Turing machine constructions in (Siegelmann and Sontag 1994, Figure 3) and elsewhere.)
**Remark 5.2**: _(bibliography)_ | I'm not sure what to cite for the study of the iterated composition \(\Delta^{L}\) and its interesting properties. The perspective here is the one from (Telgarsky 2015, 2016), but probably it exists somewhere earlier. E.g., \(\Delta^{L}\) is similar to iterated applications of the logistic map in dynamical systems,which was studied at latest in the 1940s.
**Proof of Proposition 5.1.**: The proof proceeds by induction on \(L=i\).

For the base case \(i=1\), if \(x\in[0,1)\) then directly

$$\Delta^{1}(x)=\Delta(x)=\Delta(\langle x\rangle)=\Delta(\left\langle 2^{0}x \right\rangle),$$whereas \(x=1\) means \(\Delta^{1}(x)=\Delta(0)=\Delta(\left\langle 2^{0}x\right\rangle)\).

For the inductive step, consider \(\Delta^{i+1}\). The proof can proceed by peeling individual \(\Delta\) from the left or from the right; the choice here is to peel from the right. Consider two cases.

* If \(x\in[0,1/2]\), $$\Delta^{i+1}(x)=\Delta^{i}(\Delta(x))=\Delta^{i}(2x)=\Delta(\left\langle 2^{i-1}2x \right\rangle)=\Delta(\left\langle 2^{i}x\right\rangle).$$
* If \(x\in(1/2,1]\), now additionally using a reflection property of \(\Delta\) (namely \(\Delta(z)=\Delta(1-z)\) for \(z\in[0,1]\)), $$\Delta^{i+1}(x) =\Delta^{i}(\Delta(x))=\Delta^{i}(2-2x)$$ $$=\Delta^{i-1}(\Delta(2-2x))=\Delta^{i-1}(\Delta(1-(2-2x)))= \Delta^{i}(2x-1)$$ $$=\Delta(\left\langle 2^{i}x-2^{i-1}\right\rangle)=\Delta(\left\langle 2 ^{i}x\right\rangle).$$ (If \(i=1\), use \(\Delta^{1-1}(x)=x\).)

**Remark 5.3**: _(how many ReLU9)_ Generally we won't care about inputs outside \([0,1]\), and can use two ReLUs in place of the three in the definition. But we're taking a linear combination, so the simplest way to write it is with two ReLU in one layer, then a separate ReLU layer with the linear combination. For \(\Delta^{L}\) we can be careful and stack and compress further, but that approach is not followed here.

**5.2**: **Separating shallow and deep networks**

This section will establish the following separation between constant-width deep networks and subexponential width shallow networks.

**Theorem 5.1**: _((Telgarsky 2015, 2016))_ For any \(L\geq 2\). \(f=\Delta^{L^{2}+2}\) is a ReLU network with \(3L^{2}+6\) nodes and \(2L^{2}+4\) layers, but any ReLU network \(g\) with \(\leq 2^{L}\) nodes and \(\leq L\) layers can not approximate it:

$$\int_{[0,1]}\left|f(x)-g(x)\right|\mathrm{d}x\geq\frac{1}{32}.$$

**Remark 5.4**: _(why \(L_{1}\) metric?)_ Previously, we used \(L_{2}\) and \(L_{\infty}\) to state good upper bounds on approximation; for bad approximation, we want to argue there is a large region where we fail, not just a few points, and that's why we use an \(L_{1}\) norm.

To be able to argue that such a large region exists, we don't just need the hard function \(f=\Delta^{L^{2}+2}\) to have many regions, we need them to be regularly spaced, and not bunch up. In particular, if we replaced \(\Delta\) with the similar function \(4x(1-x)\), then this proof would need to replace \(\frac{1}{32}\) with something decreasing with \(L\).

**Proof plan for Theorem 5.1** ((Telgarsky 2015, 2016)):

1. (Shallow networks have low complexity.) First we will upper bound the number of oscillations in ReLU networks. The key part of the story is that oscillations will grow polynomially in width, but _exponentially_ in depth. [ mjt(r): give explicit lemma ref]2. (There exists a _regular_, high complexity deep network.) Then we will show there exists a function, realized by a slightly deeper network, which has many oscillations, which are moreover _regularly spaced_. The need for regular spacing will be clear at the end of the proof. We have already handled this part of the proof: the hard function is \(\Delta^{L^{2}+2}\).
3. Lastly, we will use a region-counting argument to combine the preceding two facts to prove the theorem. This step would be easy for the \(L_{\infty}\) norm, and takes a bit more effort for the \(L_{1}\) norm.

**Remark 5.5**: _(bibliographic notes)_ Theorem 5.1 (([15, 2016])) was the earliest proof showing that a deep network can not be approximated by a reasonably-sized shallow network, however prior work showed a separation for _exact_ representation of deep _sum-product networks_ as compared with shallow ones (Bengio and Delalleau 2011). A sum-product network has nodes which compute affine transformations or multiplications, and thus a multi-layer sum-product network is a polynomial, and this result, while interesting, does not imply a ReLU separation.

As above, step 1 of the proof upper bounds the total possible number of affine pieces in a univariate network of some depth and width, and step 2 constructs a deep function which roughly meets this bound. Step 1 can be generalized to the multivariate case, with reasoning similar to the VC-dimension bounds in section 17. A version of step 2 appeared in prior work but for the multivariate case, specifically giving a multivariate-input network with exponentially many affine pieces, using a similar construction (Montufar et al. 2014). A version of step 2 also appeared previous as a step in a proof that recurrent networks are Turing complete, specifically a step used to perform digit extraction (Siegelmann and Sontag 1994, Figure 3).

Proceeding with the proof, first we want to argue that shallow networks have low complexity. Our notion of complexity is simply the number of affine pieces.

**Definition 5.1**: For any univariate function \(f:\mathbb{R}\to\mathbb{R}\), let \(N_{A}(f)\) denote the number of affine pieces of \(f\): the minimum cardinality (or \(\infty\)) of a partition of \(\mathbb{R}\) so that \(f\) is affine when restricted to each piece.

**Lemma 5.1**: Let \(f:\mathbb{R}\to\mathbb{R}\) be a ReLU network with \(L\) layers of widths \((m_{1},\ldots,m_{L})\) with \(m=\sum_{i}m_{i}\).

* Let \(g:\mathbb{R}\to\mathbb{R}\) denote the output of some node in layer \(i\) as a function of the input. Then the number of affine pieces \(N_{A}(g)\) satisfies $$N_{A}(g)\leq 2^{i}\prod_{j<i}m_{j}.$$
* \(N_{A}(f)\leq\left(\frac{2m}{L}\right)^{L}\).

**Remark 5.6**: Working with the ReLU really simplifies this reasoning!

Our proof will proceed by induction, using the following combination rules for piecewise affine functions.

**Lemma 5.2**: Let functions \(f,g,(g_{1},\ldots,g_{k})\), and scalars \((a_{1},\ldots,a_{k},b)\) be given.

1. \(N_{A}(f+g)\leq N_{A}(f)+N_{A}(g)\).

2. \(N_{A}(\sum_{i}a_{i}g_{i}+b)\leq\sum_{i}N_{A}(g_{i})\).
3. \(N_{A}(f\circ g)\leq N_{A}(f)\cdot N_{A}(g)\).
4. \(N_{A}\left(x\mapsto f(\sum_{i}a_{i}g_{i}(x)+b)\right)\leq N_{A}(f)\sum_{i}N_{A} (g_{i})\).

**Remark 5.7**: This immediately hints a "power of composition": we increase the "complexity" multiplicatively rather than additively!
**Remark 5.8**: It is natural and important to wonder if this exponential increase is realized in practice. Preliminary work reveals that, at least near initialization, the effective number of pieces is much smaller (Hanin and Rolnick 2019).

**Proof of Lemma 5.2.**

1. Draw \(f\) and \(g\), with vertical bars at the right boundaries of affine pieces. There are \(\leq N_{A}(f)+N_{A}(g)-1\) distinct bars, and \(f+g\) is affine between each adjacent pair of bars.
2. \(N_{A}(a_{i}g_{i})\leq N_{A}(g_{i})\) (equality if \(a_{i}\neq 0\)), thus induction with the preceding gives \(N_{A}(\sum_{i}a_{i}g_{i})=\sum_{i}N_{A}(g_{i})\), and \(N_{A}\) doesn't change with addition of constants.
3. Let \(P_{A}(g)\) denote the pieces of \(g\), and fix some \(U\in P_{A}(g)\); \(g\) is a fixed affine function along \(U\). \(U\) is an interval, and consider the pieces of \(f_{|g(U)}\); for each \(T\in P_{A}(f_{|g(U)})\), \(f\) is affine, thus \(f\circ g\) is affine (along \(U\cap g_{|U}^{-1}(T)\)), and the total number of pieces is $$\sum_{U\in P_{A}(g)}N_{A}(f_{|g(U)})\leq\sum_{U\in P_{A}(g)}N_{A}(f)\leq N_{A} (g)\cdot N_{A}(f).$$
4. Combine the preceding two.

**Remark 5.9**: The composition rule is hard to make tight: the image of each piece of \(g\) must hit all intervals of \(f\)! This is part of the motivation for the function \(\Delta\), which essentially meets this bound with every composition.

**Proof of Lemma 5.1.**

To prove the second from the first, \(N_{A}(f)\leq 2^{L}\prod_{j\leq L}m_{j}\),

$$\prod_{j\leq L}m_{j}=\exp\sum_{j\leq L}\ln m_{j}=\exp\frac{1}{L}\sum_{j\leq L} L\ln m_{j}\leq\exp L\ln\frac{1}{L}\sum_{j\leq L}m_{j}=\left(\frac{m}{L}\right)^{L}.$$

For the first, proceed by induction on layers. Base case: layer \(0\) mapping the data with identity, thus \(N_{A}(g)=1\). For the inductive step, given \(g\) in layer \(i+1\) which takes \((g_{1},\ldots,g_{m_{i}})\) from the previous layer as input,

$$N_{A}(g) =N_{A}(\sigma(b+\sum_{j}a_{j}g_{j}))\leq 2\sum_{j=1}^{m_{i}}N_{A}(g _{j})$$ $$\leq 2\sum_{j=1}^{m_{i}}2^{i}\prod_{k<i}m_{k}=2^{i+1}m_{i}\cdot \prod_{k<i}m_{k}.$$

This completes part 1 of our proof plan, upper bounding the number of affine pieces polynomially in width and exponentially in depth.

The second part of the proof was to argue that \(\Delta^{L}\) gives a high complexity, regular function: we already provided this in Proposition 5.1, which showed that \(\Delta^{L}\) gives exactly \(2^{L-1}\) copies of \(\Delta\), each shrunken uniformly by a factor of \(2^{L-1}\).

The third part is a counting argument which ensures the preceding two imply the claimed separation in \(L_{1}\) distance; details are as folllows.

**Proof of Theorem 5.1 ((Telgarsky 2015, 2016)).**

The proof proceeds by "counting triangles."

* Draw the line \(x\mapsto 1/2\) (as in the figure). The "triangles" are formed by seeing how this line intersects \(f=\Delta^{L^{2}+2}\). There are \(2^{L^{2}+1}\) copies of \(\Delta\), which means \(2^{L^{2}+2}-1\) (half-)triangles since we get two (half-)triangles for each \(\Delta\) but one is lost on the boundary of \([0,1]\). Each (half-)triangle has area \(\frac{1}{4}\cdot\frac{1}{2^{L^{2}+2}}=2^{-L^{2}-4}\).
* We will keep track of when \(g\) passes above and below this line; when it is above, we will count the triangles below; when it is above, we'll count the triangles below. Summing the area of these triangles forms a lower bound on \(\int_{[0,1]}|f-g|\).
* Using the earlier lemma, \(g\) has \(N_{A}(g)\leq(2\cdot 2^{L}/L)^{L}\leq 2^{L^{2}}\).
* For each piece, we shouldn't count the triangles at its right endpoint, or if it crosses the line, and we also need to divide by two since we're only counting triangles on one side; together $$\int_{[0,1]}|f-g| \geq[\text{number surviving triangles}]\cdot[\text{area of triangle}]$$ $$\geq\frac{1}{2}\left[2^{L^{2}+2}-1-2\cdot 2^{L^{2}}\right]\cdot \left[2^{-L^{2}-4}\right]$$ $$=\frac{1}{2}\left[2^{L^{2}+1}-1\right]\cdot\left[2^{-L^{2}-4}\right]$$ $$\geq\frac{1}{32}.$$

**Remark 5.10**: _(other depth separations)_

* Our construction was univariate. Over \(\mathbb{R}^{d}\), there exist ReLU networks with \(\text{poly}(d)\) notesin 2 hidden layers which can not be approximated by 1-hidden-layer networks unless they have \(\geq 2^{d}\) nodes (Eldan and Shamir 2015). * The 2-hidden-layer function is approximately radial; we also mentioned that these functions are difficult in the Fourier material; the quantity \(\int\|w\|\cdot|\hat{f}(w)|\mathrm{d}w\) is generally exponential in dimension for radial functions. * The proof by (Eldan and Shamir 2015) is very intricate; if one adds the condition that weights have subexponential size, then a clean proof is known (Daniely 2017). * Other variants of this problem are open; indeed, there is recent evidence that separating constant depth separations is hard, in the sense of reducing to certain complexity theoretic questions (Vardi and Shamir 2020).
* A variety of works consider connections to tensor approximation and sum product networks (Cohen and Shashua 2016; Cohen, Sharir, and Shashua 2016).
* Next we will discuss the approximation of \(x^{2}\).

**5.3**Approximating \(x^{2}\)

Why \(x^{2}\)?

* **Why it should be easy:*
* because \(x^{2}=\int_{0}^{\infty}2\sigma(x-b)\mathrm{d}b\), so we need only to uniformly place ReLUs.
* We'll use an approximate construction due to (Yarotsky 2016). It will need only \(\mathrm{poly}\log(1/\epsilon)\) nodes and depth to \(\epsilon\)-close!
* By contrast, our _shallow_ univariate approximation theorems needed \(1/\epsilon\) nodes.
* **Why we care:** with \(x^{2}\), polarization gives us multiplication: $$xy=\frac{1}{2}\left((x+y)^{2}-x^{2}-y^{2}\right).$$ From that, we get monomials, polynomials, Taylor expansions.

**Remark 5.11**: _(bibliographic notes)_: The ability to efficiently approximate \(x\mapsto x^{2}\), and consequences of this, was observed nearly in parallel by a few authors; in addition to (Yarotsky 2016) as mentioned above (whose approach is roughly followed here), in parallel was the work of (Safran and Shamir 2016), and slightly later the result was also discovered by (Rolnick and Tegmark 2017), all of these with differing perspectives and proofs.

Define \(S_{i}:=\left(\frac{0}{2^{i}},\frac{1}{2^{i}},\ldots,\frac{2^{i}}{2^{i}}\right)\); let \(h_{i}\) be the linear interpolation of \(x^{2}\) on \(S_{i}\).

Thus:

* \(h_{i}=h_{i+1}\) on \(S_{i}\).
* For \(x\in S_{i+1}\setminus S_{i}\), defining \(\epsilon=2^{-i-1}\), $$h_{i}(x)-h_{i+1}(x) =\frac{1}{2}\left(h_{i}(x-\epsilon)+h_{i}(x+\epsilon)\right)-h_{i+ 1}(x)$$ $$=\frac{1}{2}\left((x-\epsilon)^{2}+(x+\epsilon)^{2}\right)-x^{2}= \epsilon^{2}.$$

**Key point:** no dependence on \(x\)!
* Thus, for any \(x\in S_{i+1}\), $$h_{i+1}(x)=h_{i}(x)-\frac{1}{4^{i+1}}\mathbf{1}[x\in S_{i+1}\setminus S_{i}]$$
* Since \(h_{i+1}\) linearly interpolates, then \(h_{i+1}-h_{i}\) must also linearly interpolate. The linear interpolation of \(\mathbf{1}[x\in S_{i+1}\setminus S_{i}]\) is \(\Delta^{i+1}\)! Thus $$h_{i+1}=h_{i}-\frac{\Delta^{i+1}}{4^{i+1}}.$$
* Since \(h_{0}(x)=x\), then \(h_{i}(x)=x-\sum_{j=1}^{i}\frac{\Delta^{j}(x)}{4^{j}}\).

**Theorem 5.2**: _(roughly following (Yarotsky 2016))_

1. \(h_{i}\) is the piecewise-affine interpolation of \(x^{2}\) along \([0,1]\) with interpolation points \(S_{i}\).
2. \(h_{i}\) can be written as a ReLU network consisting of \(2i\) layers and \(3i\) nodes using "skip connections," or a pure ReLU network with \(2i\) layers and \(4i\) nodes.
3. \(\sup_{x\in[0,1]}|h_{i}(x)-x^{2}|\leq 4^{-i-1}\).
4. Any ReLU network \(f\) with \(\leq L\) layers and \(\leq N\) nodes satisfies $$\int_{[0,1]}(f(x)-x^{2})^{2}\mathrm{d}x\geq\frac{1}{5760(2N/L)^{4L}}.$$

**Remark 5.12**:* Can interpret as: \({\cal O}(\ln(1/\epsilon))\) layers are necessary and sufficient if we want size \({\cal O}(\ln(1/\epsilon))\). [ \(\,\mbox{\rm\small mjt}\)\(\otimes\): i need to do this explicitly]
* Last one can be beefed up to a lower bound against strongly convex functions.

**Proof.**

1. The interpolation property comes from construction/definition.
2. Since \(h_{i}=x-\sum_{j=1}^{i}\frac{\Delta^{j}}{4^{j}}\) and since \(\Delta^{j}\) requires 3 nodes and 2 layers for each new power, a worst case construction would need \(2i\) layers and \(3\sum_{j\leq i}j={\cal O}(i^{2})\) nodes, but we can reuse individual \(\Delta\) elements across the powers, and thus need only \(3i\), though the network has "skip connections" (in the ResNet sense); alternatively we can replace the skip connections with a single extra node per layer which accumulates the output, or rather after layer \(j\) outputs \(h_{j}\), which suffices since \(h_{j+1}-h_{j}=\Delta^{j+1}/4^{j+1}\).
3. Fix \(i\), and set \(\tau:=2^{-i}\), meaning \(\tau\) is the distance between interpolation points. The error between \(x^{2}\) and \(h_{i}\) is thus bounded above by $$\sup_{x\in[0,1-\tau]}\sup_{z\in[0,\tau]}\frac{\tau-z}{\tau}\left( x^{2}\right)+\frac{z}{\tau}\left(x+\tau\right)^{2}-(x+z)^{2}$$ $$=\frac{1}{\tau}\sup_{x\in[0,1-\tau]}\sup_{z\in[0,\tau]}2xz\tau+z \tau^{2}-2xz\tau-\tau z^{2}$$ $$=\frac{1}{4\tau}\sup_{x\in[0,1-\tau]}\frac{\tau^{3}}{4}=\frac{ \tau^{2}}{4}=4^{-i-1}.$$
4. By a bound from last lecture, \(N_{A}(f)\leq(2N/L)^{L}\). Using a symbolic package to differentiate, for any interval \([a,b]\), $$\min_{(c,d)}\int_{[a,b]}(x^{2}-(cx+d))^{2}\mathrm{d}x=\frac{(b-a)^{5}}{180}.$$ Let \(S\) index the subintervals of length at least \(1/(2N)\) with \(N:=N_{A}(f)\), and restrict attention to \([0,1]\). Then $$\sum_{[a,b]\in S}(b-a)=1-\sum_{[a,b]\not\in S}(b-a)\geq 1-N/(2N)=1/2.$$ Consequently, $$\int_{[0,1]}(x^{2}-f(x))^{2}\mathrm{d}x =\sum_{[a,b]\in P_{A}(f)}\int_{[a,b]\cap[0,1]}(x^{2}-f(x))^{2} \mathrm{d}x$$ $$\geq\sum_{[a,b]\in S}\frac{(b-a)^{5}}{180}$$ $$\geq\sum_{[a,b]\in S}\frac{(b-a)}{2880N^{4}}\geq\frac{1}{5760N^{ 4}}.$$

From squaring we can get many other things (still with \({\cal O}(\ln(1/\epsilon))\) depth and size.

* Multiplication (via "polarization"): $$(x,y)\mapsto xy=\frac{1}{2}\left((x+y)^{2}-x^{2}-y^{2}\right).$$* Multiplications gives polynomials.
* \(\frac{1}{x}\) and rational functions (Telgarsky 2017).
* Functions with "nice Taylor expansions" (Sobolev spaces) (Yarotsky 2016); though now we'll need size bigger than \(\ln\frac{1}{\epsilon}\):
* First we approximate each function locally with a polynomial.
* We multiply each local polynomial by a bump ((Yarotsky 2016) calls the family of bumps a "partition of unity").
* This was also reproved and connected to statistics questions by (Schmidt-Hieber 2017).

**Theorem 5.3**_(sketch, from (Yarotsky 2016; Schmidt-Hieber 2017))_Suppose \(f:\mathbb{R}^{d}\to\mathbb{R}\) has all coordinates of all partial derivatives of order up to \(r\) within \([-1,+1]\) and let \(\epsilon>0\) be given. Then there exists a \(\tilde{\mathcal{O}}(\ln(1/\epsilon)\) layer and \(\tilde{\mathcal{O}}(\epsilon^{-d/r})\) width network so that

$$\sup_{x\in[0,1]^{d}}|f(x)-g(x)|\leq\epsilon.$$

[ \(\exists\) : gross and vague, i should clean]

**Remark 5.13**: There are many papers following up on these; e.g., crawl the citation graph outwards from (Yarotsky 2016).

### Sobolev balls

Here we will continue and give a version of Yarotsky's main consequence to the approximation of \(x^{2}\): approximating functions with many bounded derivatives (by approximating their Taylor expansions), formally an approximation result against a Sobolev ball in function space.

**Remark 5.14**_(bibliographic notes)_This is an active area of work; in addition to the original work by (Yarotsky 2016), it's also worth highlighting the re-proof by (Schmidt-Hieber 2017), which then gives an interesting regression consequence. There are many other works in many directions, for instance adjusting the function class to lessen the (still bad) dependence on dimension (Montanelli, Yang, and Du 2020). These approaches all work with polynomials, but it's not clear this accurately reflects approximation power of ReLU networks (Telgarsky 2017).

**Theorem 5.4**: Suppose \(g:\mathbb{R}^{d}\to\mathbb{R}\) satisfies \(g(x)\in[0,1]\) and all partial derivatives of all orders up to \(r\) are at most \(M\). Then there exists a ReLU network with \(\mathcal{O}(k(r+d))\) layers and \(\mathcal{O}((kd+d^{2}+r^{2}d^{r}+krd^{r})s^{d})\) nodes such that

$$|f(x)-g(x)|\leq Mrd^{r}\left(s^{-r}+4d2^{d}\cdot 4^{-k}\right)+3d2^{d}\cdot 4^{-k}.\qquad\forall x\in[0,1]^{d}.$$

[ mjt(r): This isn't quite right; yarotsky claims a width \(c(d,r)/\epsilon^{d/r}\ln(1/\epsilon)\) suffices for error \(\epsilon\); need to check what I missed.]
**Remark 5.15**_(not quite right)_Matus note from Matus to Matus: Yarotsky gets width \(c(d,r)\ln(1/\epsilon)/\epsilon^{d/r}\) and mine is worse, need to track down the discrepancy.

The proof consists of the following pieces:

1. Functions in Sobolev space are locally well-approximated by their Taylor expansions; therefore we will expand the approximation of \(x^{2}\) to give approximation of general monomials in Lemma 5.4.

2. These Taylor approximations really only work locally. Therefore we need a nice way to switch between different Taylor expansions in different parts of \([0,1]^{d}\). This leads to the construction of a _partition of unity_, and is one of the other very interesting ideas in (Yarotsky 2016) (in addition to the construction of \(x^{2}\); this is done below in Lemma 5.5.

First we use squaring to obtain multiplication.

**Lemma 5.3**: For any integers \(k,l\), there exists a ReLU network \(\operatorname{prod}_{k,l}:\mathbb{R}^{l}\to\mathbb{R}\) which requires \(\mathcal{O}(kl)\) layers and \(\mathcal{O}(kl+l^{2})\) nodes such that for any \(x\in[0,1]^{l}\),

$$\left|\operatorname{prod}_{k,l}(x)-\prod_{j=1}^{l}x_{j}\right|\leq l\cdot 4^{- k},$$

and \(\operatorname{prod}_{k,l}(x)\in[0,1]\), and \(\operatorname{prod}_{k,l}(x)=0\) if any \(x_{j}\) is \(0\).

**Proof.** The proof first handles the case \(l=2\) directly, and uses \(l-1\) copies of \(\operatorname{prod}_{k,2}\) for the general case.

As such, for \((a,b)\in\mathbb{R}^{2}\), define

$$\operatorname{prod}_{k,2}(a,b):=\frac{1}{2}\left(4h_{k}((a+b)/2)-h_{k}(a)-h_{ k}(b)\right).$$

The size of this network follows from the size of \(h_{k}\) given in Theorem 5.2 (roughly following (Yarotsky 2016)), and \(\operatorname{prod}_{k,2}(a,b)=0\) when either argument is \(0\) since \(h_{k}(0)=0\). For the approximation guarantee, since every argument to each \(h_{k}\) is within \([0,1]\), then Theorem 5.2 (roughly following (Yarotsky 2016)) holds, and using the polarization identity to rewrite \(a\cdot b\) gives

$$2|\operatorname{prod}_{k,l}(a,b)-ab| =2|\operatorname{prod}_{k,l}(a,b)-\frac{1}{2}((a+b)^{2}-a^{2}-b^{ 2})|$$ $$\leq 4|h_{k}((a+b)/2)-((a+b)/2)^{2}|+|h_{k}(a)-a^{2}|+|h_{k}(b)-b ^{2}|$$ $$\leq 4\cdot 4^{-k-1}+4^{-k-1}+4^{-k-1}\leq 2\cdot 4^{-k}.$$

Now consider the case \(\operatorname{prod}_{k,i}\) for \(i>2\): this network is defined via

$$\operatorname{prod}_{k,i}(x_{1},\ldots,x_{i}):=\operatorname{prod}_{k,2}( \operatorname{prod}_{k,i-1}(x_{1},\ldots,x_{i-1}),x_{i}).$$

It is now shown by induction that this network has \(\mathcal{O}(ki+i^{2})\) nodes and \(\mathcal{O}(ki)\) layers, that it evaluates to \(0\) when any argument is zero, and lastly satisfies the error guarantee

$$\left|\operatorname{prod}_{k,i}(x_{1:i})-\prod_{j=1}^{i}x_{j}\right|\leq i4^{- k}.$$

The base case \(i=2\) uses the explicit \(\operatorname{prod}_{k,2}\) network and gaurantees above, thus consider \(i>2\). The network embeds \(\operatorname{prod}_{k,i-1}\) and another copy of \(\operatorname{prod}_{k,2}\) as subnetworks, but additionally must pass the input \(x_{i}\) forward, thus requires \(\mathcal{O}(ki)\) layers and \(\mathcal{O}(ki+i^{2})\) nodes, and evaluates to \(0\) if any argument is \(0\) by the guarantees on \(\operatorname{prod}_{k,2}\) and the inductive hypothesis. For the error estimate,

$$\left|\mathrm{prod}_{k,i}(x_{1},\ldots,x_{i})-\prod_{j=1}^{i}x_{j}\right| \leq\left|\mathrm{prod}_{k,2}(\mathrm{prod}_{k,i-1}(x_{1},\ldots,x_{ i-1}),x_{i})-x_{i}\mathrm{prod}_{k,i-1}(x_{1},\ldots,x_{i-1})\right|$$ $$+\left|x_{i}\mathrm{prod}_{k,i-1}(x_{1},\ldots,x_{i-1})-x_{i} \prod_{j=1}^{i-1}x_{j}\right|$$ $$\leq 4^{-k}+|x_{i}|\cdot\left|\mathrm{prod}_{k,i-1}(x_{1},\ldots, x_{i-1})-\prod_{j=1}^{i-1}x_{j}\right|$$ $$\leq 4^{-k}+|x_{i}|\cdot\left((i-1)4^{-k}\right)\leq i4^{-k}.$$

From multiplication we get monomials.

**Lemma 5.4**: Let degree \(r\) and input dimension \(d\) be given, and let \(N\) denote the number of monomials of degree at most \(r\). Then there exists a ReLU network \(\mathrm{mono}_{k,r}:\mathbb{R}^{d}\to\mathbb{R}^{N}\) with \(\mathcal{O}(kr)\) layers and \(\mathcal{O}(d^{r}(kr+r^{2}))\) nodes so that for any vector of exponents \(\vec{\alpha}\) corresponding to a monomial of degree at most \(r\), meaning \(\vec{\alpha}\geq 0\), \(\sum_{i}\alpha_{i}\leq r\), and \(x^{\vec{\alpha}}:=\prod_{i=1}^{d}x_{i}^{\alpha_{i}}\), then the output coordinate of \(\mathrm{mono}_{k,r}\) corresponding to \(\vec{\alpha}\), written \(\mathrm{mono}_{k,r}(x)_{\vec{\alpha}}\) for convenience, satisfies

$$\left|\mathrm{mono}_{k,r}(x)_{\vec{\alpha}}-x^{\vec{\alpha}}\right|\leq r4^{-k }\qquad\forall x\in[0,1]^{d}.$$

**Proof.**\(\mathrm{mono}_{k,r}\) consists of \(N\) parallel networks, one for each monomial. As such, given any \(\vec{\alpha}\) of degree \(q\leq r\), to define coordinate \(\vec{\alpha}\) of \(\mathrm{mono}_{k,r}\), first rewrite \(\alpha\) as a vector \(v\in\{1,\ldots,d\}^{q}\), whereby

$$x^{\vec{\alpha}}:=\prod_{i=1}^{q}x_{v_{i}}.$$

Define

$$\mathrm{mono}_{k,r}(x)_{\vec{\alpha}}:=\mathrm{prod}_{k,q}(x_{v_{1}},\ldots,x _{v_{q}}),$$

whereby the error estimate follows from Lemma 5.3, and the size estimate follows by multiplying the size estimate from Lemma 5.3 by \(N\), and noting \(N\leq d^{r}\).

Next we construct the approximate partition of unity.

**Lemma 5.5**: For any \(s\geq 1\), let \(\mathrm{part}_{k,s}:\mathbb{R}^{d}\to\mathbb{R}^{(s+1)^{d}}\) denote an approximate partition of unity implemented by a ReLU network, detailed as follows.

1. For any vector \(v\in S:=\{0,1/s,\ldots,s/s\}^{d}\), there is a corresponding coordinate \(\mathrm{part}_{k,s}(\cdot)_{v}\), and this coordinate is only supported locally around \(v\), meaning concretely that \(\mathrm{part}_{k,s}(x)_{v}\) is zero for \(x\not\in\prod_{j=1}^{d}[v_{j}-1/s,v_{j}+1/s]\).
2. For any \(x\in[0,1]^{d}\), \(|\sum_{v\in S}\mathrm{part}_{k,s}(x)_{v}-1|\leq d2^{d}4^{-k}\).
3. \(\mathrm{part}_{k,s}\) can be implemented by a ReLU network with \(\mathcal{O}(kd)\) layers and \(\mathcal{O}((kd+d^{2})s^{d})\) nodes.

**Proof.** Set \(N:=(s+1)^{d}\), and let \(S\) be any enumeration of the vectors in the grid \(\{0,1/s,\ldots,s/s\}^{d}\).

Define first a univariate bump function

$$h(a):=\sigma(sa+1)-2\sigma(sa)+\sigma(sa-1)=\begin{cases}1+sa&a\in[-1/s,0),\\ 1-sa&a\in[0,1/s]\\ 0&\text{o.w.}.\end{cases}$$

For any \(v\in S\), define

$$f_{v}(x):=\text{prod}_{k,d}(h(x_{1}-v_{1}),\ldots,h(x_{d}-v_{d})).$$

By Lemma 5.3,

$$\sup_{x\in[0,1]^{d}}|f_{v}(x)-\prod_{j=1}^{d}h(x_{j}-v_{j})|\leq d4^{-k}.$$

Each coordinate of the output of \(\text{part}_{k,s}\) corresponds to some \(v\in S\); in particular, define

$$\text{part}_{k,s}(x)_{v}:=f_{v}(x).$$

As such, by the definition of \(f_{v}\), and Lemma 5.3, and since \(|S|\leq(s+1)^{d}\), then \(\text{part}_{k,s}\) can be written with \(kd\) layers and \(\mathcal{O}((kd+d^{2})s^{d})\) nodes. The local support claim for \(\text{part}_{k,s}(\cdot)_{v}\) follows by construction. For the claim of approximate partition of unity, using \(U\subseteq S\) to denote the local set of coordinates corresponding to nonzero coordinates of \(\text{part}_{k,s}\) (which has \(|U|\leq 2^{d}\) by the local support claim),

$$|\sum_{v\in S}\text{part}_{k,s}(x)_{v}-1| =|\sum_{v\in U}(\text{part}_{k,s}(x)_{v}-\prod_{j=1}^{d}h(x_{j}-v _{j})+\prod_{j=1}^{d}h(x_{j}-v_{j})-1|$$ $$\leq\sum_{v\in U}|\text{part}_{k,s}(x)_{v}-\prod_{j=1}^{d}h(x_{j} -v_{j})+|\sum_{v\in U}\prod_{j=1}^{d}h(x_{j}-v_{j})-1|$$ $$\leq 2^{d}d4^{-k}+|\sum_{v\in U}\prod_{j=1}^{d}h(x_{j}-v_{j})-1|.$$

It turns out the last term of the sum is \(0\), which completes the proof: letting \(u\) denote the lexicographically smallest element in \(U\) (i.e., the "bottom left corner"),

$$|\sum_{v\in U}\prod_{j=1}^{d}h(x_{j}-v_{j})-1| =|\sum_{w\in\{0,1/s\}^{d}}\prod_{j=1}^{d}h((x-u+w)_{j})-1|$$ $$=|\prod_{j=1}^{d}\sum_{w_{j}\in\{0,1/s\}}h((x-u+w)_{j})-1|$$ $$=|\prod_{j=1}^{d}(h(x_{j}-u_{j})+h(x_{j}-u_{j}+1/s))-1|,$$

which is \(0\) because \(z:=x-u\in[0,1/s]^{d}\) by construction, and using the case analysis of \(h\) gives

$$h(z_{j})+h(z_{j}+1/s)=(1+sz_{j})+(1-s(z_{j}+1/s))=1$$

as desired.

Finally we are in shape to prove Theorem 5.4.

**Proof of Theorem 5.4.** The ReLU network for \(f\) will combine \(\operatorname{part}_{k,s}\) from Lemma 5.5 with \(\operatorname{mono}_{k,r}\) from Lemma 5.4 via approximate multiplication, meaning \(\operatorname{prod}_{k,2}\) from Lemma 5.3.

In detail, let the grid \(S:=\{0,1/s,\ldots,s/s\}^{d}\) be given as in the statement of Lemma 5.5. For each \(v\in S\), let \(p_{v}:\mathbb{R}^{d}\to\mathbb{R}\) denote the Taylor expansion of degree \(r\) at \(v\); by a standard form of the Taylor error, for any \(x\in[0,1]^{d}\) with \(\|x-v\|_{\infty}\leq 1/s\),

$$|p_{v}(x)-g(x)|\leq\frac{Md^{r}}{r!}\|v-x\|_{\infty}^{r}\leq\frac{Md^{r}}{r!s^{ r}}.$$

Next, let \(w_{v}\) denote the Taylor coefficients forming \(p_{v}\), and define \(f_{v}:\mathbb{R}^{d}\to\mathbb{R}\) as \(x\mapsto w_{v}^{\mathsf{T}}\operatorname{mono}_{k,r}(x-v)\), meaning approximate \(p_{v}\) by taking the linear combination with weights \(w_{v}\) of the approximate monomials in \(x\mapsto\operatorname{mono}_{k,r}(x-v)\). By Lemma 5.4, since there are at most \(d^{r}\) terms, the error is at most

$$|f_{v}(x)-p_{v}(x)|=|\sum_{\vec{\alpha}}(w_{v})_{\vec{\alpha}}(\operatorname{ mono}_{k,r}(x-v)_{\vec{\alpha}}-(x-v)^{\vec{\alpha}})|\leq\sum_{\vec{\alpha}}|(w_ {v})_{\vec{\alpha}}|r4^{-k}\leq Mrd^{r}4^{-k}.$$

[ : just realized a small issue that negative inputs might occur; can do some shifts or reflections or whatever to fix.]

The final network is now obtained by using \(\operatorname{prod}_{k,2}\) to approximately multiply each approximate Taylor expansion \(f_{v}\) by the corresponding locally-supported approximate partition of unity element \(\operatorname{part}_{k,s}(x)_{v}\); in particular, define

$$f(x):=\sum_{v\in S}\operatorname{prod}_{k,2}(f_{v}(x),\operatorname{part}_{k, s}(x)_{v}).$$

Then, using the above properties and the fact that the partition of unity is locally supported, letting \(U\subseteq S\) denote the set of at most \(2^{d}\) active elements,

$$|f(x)-g(x)| \leq\left|\sum_{v\in S}\operatorname{prod}_{k,2}(f_{v}(x), \operatorname{part}_{k,s}(x)_{v})-\sum_{v\in S}f_{v}(x)\operatorname{part}_{k,s}(x)_{v}\right|$$ $$+\left|\sum_{v\in S}f_{v}(x)\operatorname{part}_{k,s}(x)_{v}- \sum_{v\in S}p_{v}(x)\operatorname{part}_{k,s}(x)_{v}\right|$$ $$+\left|\sum_{v\in S}p_{v}(x)\operatorname{part}_{k,s}(x)_{v}- \sum_{v\in S}g(x)\operatorname{part}_{k,s}(x)_{v}\right|$$ $$+\left|\sum_{v\in S}g(x)\operatorname{part}_{k,s}(x)_{v}-g(x)\right|$$ $$\leq 2|U|4^{-k}+Mrd^{r}4^{-k}(1+d2^{d}4^{-k})+\frac{Md^{r}}{r!s^ {r}}(1+d2^{d}4^{-k})+|f(x)|d2^{d}4^{-k}$$ $$\leq Mrd^{r}\left(s^{-r}+4d2^{d}\cdot 4^{-k}\right)+3d2^{d} \cdot 4^{-k}.$$

[ : The input to \(\operatorname{prod}_{k,2}\) can exceed 1. for a maximally lazy fix, I should just clip its input.]

**6** **Optimization: preface**Classically, the purpose of optimization is to approximately minimize (or maximize) an _objective function_\(f\) over a domain \(S\):

$$\min_{w\in S}f(w).$$

**A core tension** in the use of optimization in machine learning is that we would like to minimize the _population_ risk \(\mathcal{R}(w):=\mathbb{E}\,\ell(Yf(X;w))\); however, we only have access to the _empirical_ risk \(\widehat{\mathcal{R}}(w):=n^{-1}\sum_{i}\ell(y_{i}f(x_{i};w))\).

As a result, when choosing a \(w_{t}\), we not only care that \(\widehat{\mathcal{R}}(w_{t})\) is small, but also other good properties which may indicate \(\mathcal{R}(w_{t})\) is small as well. Foremost amongst these are that \(w_{t}\) has low norm, but there are other possibilities.

**Outline.**

* We will cover primarily first-order methods, namely gradient descent $$w_{t+1}:=w_{t}-\eta_{t}\nabla\widehat{\mathcal{R}}(w_{t}),$$ as well as the gradient flow $$\frac{\mathrm{d}w}{\mathrm{d}t}=\dot{w}(t)=-\nabla\widehat{\mathcal{R}}(w(t)).$$ These dominate machine learning since:
* They have low per-iteration complexity (which can be reduced further with stochastic gradients); classical optimization developed many methods with higher per-iteration cost but a lower number of iterations, but the high accuracy these give is not important here since our true objective is unknown anyway.
* It seems they might have additional favorable properties; e.g., we will highlight the preference for low-norm solutions of first-order methods.
* First we'll cover classical smooth and convex opt, including strong convexity and stochastic gradients. Here our analysis differs from the literature by generally not requiring boundedness or existence of minima. Concretely, many proofs will use an arbitrary reference point \(z\) in place of an optimum \(\bar{w}\) (which may not exist); this arbitrary \(z\) will be used effectively in the margin maximization lectures.
* Then we will cover topics closer to deep learning, including gradient flow in a smooth shallow NTK case, and a few margin maximization cases, with a discussion of nonsmoothness.

**Remark 6.1**:
* Even though our models are not convex (and \(\widehat{\mathcal{R}}\) is not convex in the parameters), our losses will always be convex.
* Analyzing gradient flow simplifies analyses, but in some cases it is difficult or completely unclear how to reproduce the same rates with gradient descent, and secondly it isn't clear that they _should_ have the same rates or convergence properties; in deep learning, for instance, the role of step size is not well-understood, whereas approximating gradient flow suggests small step sizes.

* A _regularized ERM_ objective has the form \(w\mapsto\widehat{\mathcal{R}}(w)+P(w)\), where (for example) \(P(w):=\lambda\|w\|^{2}/2\). We will not discuss these extensively, and we will similarly hardly discuss constrained optimization.
* A good introductory text on various optimization methods in machine learning is (Bubeck 2014); for more on convex optimization, see for instance (Nesterov 2003), and for more on convex analysis, see for instance (Bubeck 2014; Borwein and Lewis 2000).

[MISSING_PAGE_POST]

[mjt():.

* **Benefits of depth for optimization.** Most of these works are either for shallow networks, or the analysis allows depth but _degrades_ with increasing depth, in contrast with practical observations. A few works now are trying to show how depth can help optimization; one perspective is that sometimes it can accelerate convergence (Arora, Cohen, and Hazan 2018; Arora, Cohen, et al. 2018a).
* **Other first-order optimizers,** e.g., Adam. There is recent work on these but afaik it doesn't capture why these work well on many deep learning tasks.
* **Further analysis of overparameterization.** Overparameterization makes many aspects of the optimization problem nicer, in particular in ways not investigated in these notes (Shamir 2018; S. Du and Hu 2019).
* **Hardness of learning and explicit global solvers.** Even in simple cases, network training is NP-hard, but admits various types of approximation schemes (Goel et al. 2020; Diakonikolas et al. 2020).

## 7 Semi-classical convex optimization

First we will revisit classical convex optimization ideas. Our presentation differs from the normal one in one key way: we state nearly results without any assumption of a minimizer, but instead use an arbitrary _reference point_\(z\in\mathbb{R}^{p}\). We will invoke these bounds later in settings where the minimum may not exist, but the problem structure suggests good choices for \(z\) (see e.g., Lemma 10.1).

[ mjt(): if i include ReLU ntk I can also use it there.]

### Smooth objectives in ML

We say "\(\widehat{\mathcal{R}}\) is \(\beta\)-smooth" to mean \(\beta\)-Lipschitz gradients:

$$\|\nabla\widehat{\mathcal{R}}(w)-\nabla\widehat{\mathcal{R}}(v)\|\leq\beta\|w- v\|.$$

(The math community says "smooth" for \(C^{\infty}\).) We primarily invoke smoothness via the key inequality

$$\widehat{\mathcal{R}}(v)\leq\widehat{\mathcal{R}}(w)+\left\langle\nabla \widehat{\mathcal{R}}(w),v-w\right\rangle+\frac{\beta}{2}\|v-w\|^{2}.$$

In words: \(f\) can be upper bounded with the _convex_ quadratic

$$v\mapsto\frac{\beta}{2}\|v-w\|^{2}+\left\langle\nabla\widehat{\mathcal{R}}(w),v-w\right\rangle+\widehat{\mathcal{R}}(w),$$

which shares tangent and function value with \(\widehat{\mathcal{R}}\) at \(w\). (The first definition also implies that we are lower bounded by _concave_ quadratics.)

**Remark 7.1**: Smoothness is _trivially_ false for standard deep networks: the ReLU is not even differentiable. However, many interesting properties carry over, and many lines of research proceed by trying to make these properties carry over, so at the very least, it's good to understand.

_A key consequence:_ we can guarantee gradient descent does not increase the objective. Consider gradient iteration \(w^{\prime}=w-\frac{1}{\beta}\nabla\widehat{\mathcal{R}}(w)\), then smoothness implies

$$\widehat{\mathcal{R}}(w^{\prime})\leq\widehat{\mathcal{R}}(w)-\left\langle \widehat{\mathcal{R}}(w),\widehat{\mathcal{R}}(w)/\beta\right\rangle+\frac{1}{ 2\beta}\|\widehat{\mathcal{R}}(w)\|^{2}=\widehat{\mathcal{R}}(w)-\frac{1}{2 \beta}\|\nabla\widehat{\mathcal{R}}(w)\|^{2},$$

and \(\|\nabla\widehat{\mathcal{R}}(w)\|^{2}\leq 2\beta(\widehat{\mathcal{R}}(w)- \widehat{\mathcal{R}}(w^{\prime}))\). With deep networks, we'll produce similar bounds but in other ways.

As an exercise, let's prove the earlier smoothness consequence. Considering the curve \(t\mapsto\widehat{\mathcal{R}}(w+t(v-w))\) along \([0,1]\),

$$\left|\widehat{\mathcal{R}}(v)-\widehat{\mathcal{R}}(w)-\left\langle \nabla\widehat{\mathcal{R}}(w),v-w\right\rangle\right|$$ $$=\left|\int_{0}^{1}\left\langle\nabla\widehat{\mathcal{R}}(w+t(v -w)),v-w\right\rangle\mathrm{d}t-\left\langle\nabla\widehat{\mathcal{R}}(w),v -w\right\rangle\right|$$ $$\leq\int_{0}^{1}\left|\left\langle\nabla\widehat{\mathcal{R}}(w +t(v-w))-\nabla\widehat{\mathcal{R}}(w),v-w\right\rangle\right|\mathrm{d}t$$ $$\leq\int_{0}^{1}\|\nabla\widehat{\mathcal{R}}(w+t(v-w))-\nabla \widehat{\mathcal{R}}(w)\|\cdot\|v-w\|\mathrm{d}t$$ $$\leq\int_{0}^{1}t\beta\|v-w\|^{2}\mathrm{d}t$$ $$=\frac{\beta}{2}\|v-w\|^{2}.$$

**Example 7.1**: Define \(\widehat{\mathcal{R}}(w):=\frac{1}{2}\|Xw-y\|^{2}\), and note \(\nabla\widehat{\mathcal{R}}(w)=X^{\intercal}(Xw-y)\). For any \(w,w^{\prime}\),

$$\widehat{\mathcal{R}}(w^{\prime}) =\frac{1}{2}\|Xw^{\prime}-Xw+Xw-y\|^{2}$$ $$=\frac{1}{2}\|Xw^{\prime}-Xw\|^{2}+\left\langle Xw^{\prime}-Xw,Xw -y\right\rangle+\frac{1}{2}\|Xw-y\|^{2}$$ $$=\frac{1}{2}\|Xw^{\prime}-Xw\|^{2}+\left\langle w^{\prime}-w, \widehat{\mathcal{R}}(w)\right\rangle+\widehat{\mathcal{R}}(w).$$

Since \(\frac{\sigma_{\min}(X)}{2}\|w^{\prime}-w\|^{2}\leq\frac{1}{2}\|Xw^{\prime}-Xw \|^{2}\leq\frac{\sigma_{\max}(X)}{2}\|w^{\prime}-w\|^{2}\), thus \(\widehat{\mathcal{R}}\) is \(\sigma_{\max}(X)\)-smooth (and \(\sigma_{\min}\)-strongly-convex, as we'll discuss).

The smoothness bound holds **with equality** if we use the seminorm \(\|v\|_{X}=\|Xv\|\). We'll (maybe?) discuss smoothness wrt other norms in homework.

[ mjt(r): I should use \(\mathcal{L}\) not \(\widehat{\mathcal{R}}\) since unnormalized.]

**7.1.1**: **Convergence to stationary points**

Consider first the gradient iteration

$$w^{\prime}:=w-\eta\nabla\widehat{\mathcal{R}}(w),$$where \(\eta\geq 0\) is the step size. When \(f\) is \(\beta\) smooth but not necessarily convex, the smoothness inequality directly gives

$$\begin{split}\widehat{\mathcal{R}}(w^{\prime})&\leq \widehat{\mathcal{R}}(w)+\left\langle\nabla\widehat{\mathcal{R}}(w),w^{\prime}- w\right\rangle+\frac{\beta}{2}\|w^{\prime}-w\|^{2}\\ &=\widehat{\mathcal{R}}(w)-\eta\|\nabla\widehat{\mathcal{R}}(w) \|^{2}+\frac{\beta\eta^{2}}{2}\|\nabla\widehat{\mathcal{R}}(w)\|^{2}\\ &=\widehat{\mathcal{R}}(w)-\eta\left(1-\frac{\beta\eta}{2}\right) \|\nabla\widehat{\mathcal{R}}(w)\|^{2}.\end{split} \tag{3}$$

If we choose \(\eta\) appropriately (\(\eta\leq 2/\beta\)) then: either we are near a critical point (\(\nabla\widehat{\mathcal{R}}(w)\approx 0\)), or we can decrease \(\widehat{\mathcal{R}}\).

Let's refine our notation to tell iterates apart:

1. Let \(w_{0}\) be given.
2. Recurse: \(w_{i+1}:=w_{i}-\eta_{i}\nabla\widehat{\mathcal{R}}(w_{i})\).

[ mjt(): I changed indexing (2021-09-23), need to update everywhere...]

Rearranging our iteration inequality eq. 3 and summing over \(i<t\),

$$\begin{split}\sum_{i<t}\eta_{i}\left(1-\frac{\beta\eta_{i}}{2} \right)\|\nabla\widehat{\mathcal{R}}(w_{i})\|^{2}&\leq\sum_{i<t} \left(\widehat{\mathcal{R}}(w_{i})-\widehat{\mathcal{R}}(w_{i+1})\right)\\ &=\widehat{\mathcal{R}}(w_{0})-\widehat{\mathcal{R}}(w_{t}).\end{split}$$

We can summarize these observations in the following theorem.

**Theorem 7.1**.\(\big{|}\) Let \((w_{i})_{i\geq 0}\) be given by gradient descent on \(\beta\)-smooth \(\widehat{\mathcal{R}}\).

* If \(\eta_{i+1}\in[0,2/\beta]\), then \(\widehat{\mathcal{R}}(w_{i+1})\leq\widehat{\mathcal{R}}(w_{i})\).
* If \(\eta_{i}:=\eta\in[0,2/\beta]\) is constant across \(i\), $$\begin{split}\min_{i<t}\|\nabla\widehat{\mathcal{R}}(w_{i})\|^{ 2}&\leq\frac{1}{t}\sum_{i<t}\|\nabla\widehat{\mathcal{R}}(w_{i}) \|^{2}\\ &\leq\frac{2}{t\eta(2-\eta\beta)}\left(\widehat{\mathcal{R}}(w_{0} )-\widehat{\mathcal{R}}(w_{t})\right)\\ &\leq\frac{2}{t\eta(2-\eta\beta)}\left(\widehat{\mathcal{R}}(w_{0 })-\inf_{w}\widehat{\mathcal{R}}(w)\right).\end{split}$$ This final expression is minimized by \(\eta:=\frac{1}{\beta}\), which gives $$\min_{i<t}\|\nabla\widehat{\mathcal{R}}(w_{i})\|^{2}\leq\frac{1}{t}\sum_{i<t} \|\nabla\widehat{\mathcal{R}}(w_{i})\|^{2}\leq\frac{2\beta}{t}\left(\widehat {\mathcal{R}}(w_{0})-\widehat{\mathcal{R}}(w_{t})\right)\leq\frac{2\beta}{t} \left(\widehat{\mathcal{R}}(w_{0})-\inf_{w}\widehat{\mathcal{R}}(w)\right).$$

**Remark 7.2**

* We have no guarantee about the last iterate \(\|\nabla\widehat{\mathcal{R}}(w_{t})\|\): we may get near a flat region at some \(i<t\), but thereafter bounce out. With a more involved proof, we can guarantee we bounce out (J. D. Lee et al. 2016), but there are cases where the time is exponential in dimension.

* This derivation is at the core of many papers with a "local optimization" (stationary point or local optimum) guarantee for gradient descent.
* In a bit more detail, the step size \(1/\beta\) is the result of minimizing the quadratic provided by smoothness: $$w-\frac{1}{\beta}\nabla\widehat{\mathcal{R}}(w) =\operatorname*{arg\,min}_{w^{\prime}}\left(\widehat{\mathcal{R}} (w)+\left\langle\nabla\widehat{\mathcal{R}}(w),w^{\prime}-w\right\rangle+\frac {\beta}{2}\|w^{\prime}-w\|^{2}\right)$$ $$=\operatorname*{arg\,min}_{w^{\prime}}\left(\left\langle\nabla \widehat{\mathcal{R}}(w),w^{\prime}\right\rangle+\frac{\beta}{2}\|w^{\prime}- w\|^{2}\right).$$ This relates to _proximal descent_ and _mirror descent_ generalizations of gradient descent.
* In \(t\) iterations, we found a point \(w\) with \(\|\nabla\widehat{\mathcal{R}}(w)\|\leq\sqrt{2\beta/t}\). We can do better with Nesterov-Polyak cubic regularization: by choosing the next iterate according to $$\operatorname*{arg\,min}_{w^{\prime}}\left(\widehat{\mathcal{R}} (w)+\left\langle\nabla\widehat{\mathcal{R}}(w),w^{\prime}-w\right\rangle\right.$$ $$\qquad\qquad+\left.\frac{1}{2}\left\langle\nabla^{2}\widehat{ \mathcal{R}}(w)(w^{\prime}-w),w^{\prime}-w\right\rangle+\frac{L}{6}\|w^{ \prime}-w\|^{3}\right)$$ where \(\|\nabla^{2}\widehat{\mathcal{R}}(x)-\nabla^{2}\widehat{\mathcal{R}}(y)\|\leq L \|x-y\|\), then after \(t\) iterations, some iterate \(w_{j}\) with \(j\leq t\) satisfies $$\|\nabla\widehat{\mathcal{R}}(w_{j})\|\leq\frac{\mathcal{O}(1)}{t^{2/3}}, \qquad\lambda_{\min}\left(\nabla^{2}\widehat{\mathcal{R}}(w_{j})\right)\geq- \frac{\mathcal{O}(1)}{t^{1/3}}.$$ Note: it is not obvious that the above cubic can be solved efficiently, but indeed there are various ways. If we go up a few higher derivatives, it becomes NP-hard. Original used an eigenvalue solver for this cubic polynomial (Nesterov and Polyak 2006). Other approaches are given by (Carmon and Duchi 2018; Jin et al. 2017), amongst many others.

**Gradient flow version.** Using FTC, chain rule, and definition,

$$\widehat{\mathcal{R}}(w(t))-\widehat{\mathcal{R}}(w(0)) =\int_{0}^{t}\left\langle\nabla\widehat{\mathcal{R}}(w(s)),\dot{w }(s)\right\rangle\mathrm{d}s$$ $$=-\int_{0}^{t}\|\nabla\widehat{\mathcal{R}}(w(s))\|^{2}\mathrm{d}s$$ $$\leq-t\inf_{s\in[0,t]}\|\nabla\widehat{\mathcal{R}}(w(s))\|^{2},$$

which can be summarized as follows.

**Theorem 7.2**: For the gradient flow,

$$\inf_{s\in[0,t]}\|\nabla\widehat{\mathcal{R}}(w(s))\|^{2}\leq\frac{1}{t}\left( \widehat{\mathcal{R}}(w(0))-\widehat{\mathcal{R}}(w(t))\right).$$

**Remark 7.3**: GD: \(\min_{i<t}\|\nabla\widehat{\mathcal{R}}(w_{i})\|^{2}\leq\frac{2\beta}{t}\left( \widehat{\mathcal{R}}(w_{0})-\widehat{\mathcal{R}}(w_{t})\right)\).

* \(\beta\) is from step size.
* "2" is from the order smoothness term (avoided in GF).

If \(\widehat{\mathcal{R}}\) is differentiable and _convex_, then it is bounded below by its first-order approximations:

$$\widehat{\mathcal{R}}(w^{\prime})\geq\widehat{\mathcal{R}}(w)+\left\langle\nabla \widehat{\mathcal{R}}(w),w^{\prime}-w\right\rangle\qquad\forall w,w^{\prime}.$$

**Theorem 7.3**: Suppose \(\widehat{\mathcal{R}}\) is \(\beta\)-smooth and convex, and \((w_{i})_{\geq 0}\) given by GD with \(\eta_{i}:=1/\beta\). Then for any \(z\),

$$\widehat{\mathcal{R}}(w_{t})-\widehat{\mathcal{R}}(z)\leq\frac{\beta}{2t} \left(\|w_{0}-z\|^{2}-\|w_{t}-z\|^{2}\right).$$

**Remark 7.4**: The reference point \(z\) allows us to use this bound effectively when \(\widehat{\mathcal{R}}\) lacks an optimum, or simply when the optimum is very large. For an example of such an application of \(z\), see the margin maximization material (e.g., Lemma 10.1).
**Proof.** By convexity and the earlier smoothness inequality \(\|\nabla\widehat{\mathcal{R}}(w)\|^{2}\leq 2\beta(\widehat{\mathcal{R}}(w)- \widehat{\mathcal{R}}(w^{\prime}))\),

$$\|w^{\prime}-z\|^{2} =\|w-z\|^{2}-\frac{2}{\beta}\left\langle\nabla\widehat{\mathcal{ R}}(w),w-z\right\rangle+\frac{1}{\beta^{2}}\|\nabla\widehat{\mathcal{R}}(w) \|^{2}$$ $$\leq\|w-z\|^{2}+\frac{2}{\beta}(\widehat{\mathcal{R}}(z)-\widehat {\mathcal{R}}(w))+\frac{2}{\beta}(\widehat{\mathcal{R}}(w)-\widehat{\mathcal{ R}}(w^{\prime}))$$ $$=\|w-z\|^{2}+\frac{2}{\beta}(\widehat{\mathcal{R}}(z)-\widehat{ \mathcal{R}}(w^{\prime})).$$

Rearranging and applying \(\sum_{i<t}\),

$$\frac{2}{\beta}\sum_{i<t}(\widehat{\mathcal{R}}(w_{i+1})-\widehat{\mathcal{R} }(z))\leq\sum_{i<t}\left(\|w_{i}-z\|^{2}-\|w_{i+1}-z\|^{2}\right)$$

The final bound follows by noting \(\widehat{\mathcal{R}}(w_{i})\geq\widehat{\mathcal{R}}(w_{t})\), and since the right hand side telescopes.

**Remark 7.5**: _(characterizing convexity)_ There are many ways to characterize convexity. As follows are a few different versions; standard texts with more characterizations and more generality (e.g., using infinite output values to model constraint sets, and using subdifferentials as a meaningful surrogate for gradients for nondifferentiable convex functions) are Hiriart-Urruty and Lemarechal (2001).

* **(Epigraph view.)** Let \(\mathrm{epi}(f)\), the _epigraph_ of \(f:\mathbb{R}^{d}\to\mathbb{R}\), denote the subset of \(\mathbb{R}^{n+1}\) that is equal to or above \(f\): $$\mathrm{epi}(f):=\left\{(x,y)\in\mathbb{R}^{d+1}:y\geq f(x)\right\}.$$ \(f\) is _convex_ when \(\mathrm{epi}(f)\) is a convex set (meaning \([x,x^{\prime}]:=\{\alpha x+(1-\alpha)x^{\prime}:\alpha\in[0,1]\}\subseteq \mathrm{epi}(f)\) whenever \(\{x,x^{\prime}\}\subseteq\mathrm{epi}(f)\)), \(f\) is _strictly convex_ when \(\mathrm{epi}(f)\) is convex and tangents to \(\mathrm{epi}(f)\) intersect only one point, and \(f\) is _strongly convex_ when at any point \((x,y)\) on the boundary of \(\mathrm{epi}(f)\) meaning \(f(x)=y))\), we can find a quadratic \(Q:\mathbb{R}^{d}\to\mathbb{R}\) with \(Q(x)=y\) and \(\mathrm{epi}(f)\subseteq\mathrm{epi}(Q)\).

* **(Function value ("zeroth-order") view.)** Given \(\alpha\in[0,1]\) and any \(x,x^{\prime}\), \(f\) is convex when $$f(\alpha x+(1-\alpha)x^{\prime})\leq\alpha f(x)+(1-\alpha)f(x^{\prime}),$$ strictly convex when for any \(\alpha\in(0,1)\) and \(x\neq x^{\prime}\) $$f(\alpha x+(1-\alpha)x^{\prime})<\alpha f(x)+(1-\alpha)f(x^{\prime}),$$ and \(\lambda\)-strongly-convex when $$f(\alpha x+(1-\alpha)x^{\prime})\leq\alpha f(x)+(1-\alpha)f(x^{\prime})-\frac{ \lambda\alpha(1-\alpha)}{2}\|x-x^{\prime}\|^{2}.$$ We also have \(f\) is \(\lambda\)-strongly convex iff \(f-\frac{\lambda}{2}\|\cdot\|^{2}\) is convex.
* **(Gradient ("first-order") view.)** When \(f\) is differentiable, it is convex when $$f(x^{\prime})\geq f(x)+\left\langle\nabla f(x),x^{\prime}-x\right\rangle\qquad \forall x,x^{\prime},$$ strictly convex when $$f(x^{\prime})>f(x)+\left\langle\nabla f(x),x^{\prime}-x\right\rangle\qquad \forall x\neq x^{\prime},$$ and \(\lambda\)-strongly-convex when $$f(x^{\prime})\geq f(x)+\left\langle\nabla f(x),x^{\prime}-x\right\rangle+\frac {\lambda}{2}\|x-x^{\prime}\|^{2}\qquad\forall x\neq x^{\prime}.$$ We can add instantiate these inequalities for any pair \((x,x^{\prime})\) and the reverse \((x^{\prime},x)\) and combine them and get that convexity implies $$0\leq\left\langle\nabla f(x^{\prime})-\nabla f(x),x^{\prime}-x\right\rangle \qquad\forall x,x^{\prime},$$ strict convexity implies $$0<\left\langle\nabla f(x^{\prime})-\nabla f(x),x^{\prime}-x\right\rangle\qquad \forall x\neq x^{\prime},$$ and strong convexity implies $$\lambda\|x-x^{\prime}\|^{2}\leq\left\langle\nabla f(x^{\prime})-\nabla f(x),x^ {\prime}-x\right\rangle\qquad\forall x,x^{\prime}.$$ There are also versions of all of these for nondifferentiable convex functions using _subdifferentials_, see (Hiriart-Urruty and Lemarechal 2001).
* **(Hessian ("first-order") view.)** When \(f\) is twice-differentiable, convexity implies $$\nabla^{2}f(x)\succeq 0\qquad\forall x,$$ strict convexity implies $$\nabla^{2}f(x)\succ 0\qquad\forall x,$$ and \(\lambda\)-strong-convexity implies $$\nabla^{2}f(x)\succeq\lambda I\qquad\forall x.$$For GF, we use the same potential, but indeed start from the telescoping sum, which can be viewed as a Riemann sum corresponding to the following application of FTC:

$$\frac{1}{2}\|w(t)-z\|_{2}^{2}-\frac{1}{2}\|w(0)-z\|_{2}^{2} =\frac{1}{2}\int_{0}^{t}\frac{\mathrm{d}}{\mathrm{d}s}\|w(s)-z\|_{ 2}^{2}\mathrm{d}s$$ $$=\int_{0}^{t}\left\langle\frac{\mathrm{d}w}{\mathrm{d}s},w(s)-z \right\rangle\mathrm{d}s$$ $$=\int_{0}^{t}\left\langle\nabla\widehat{\mathcal{R}}(w(s)),z-w(s) \right\rangle\mathrm{d}s$$ $$\leq\int_{0}^{t}\left(\widehat{\mathcal{R}}(z)-\widehat{\mathcal{ R}}(w(s))\right)\mathrm{d}s.$$

**Theorem 7.4**: For any \(z\in\mathbb{R}^{d}\), GF satisfies

$$t\widehat{\mathcal{R}}(w(t))+\frac{1}{2}\|w(t)-z\|_{2}^{2} \leq\int_{0}^{t}\widehat{\mathcal{R}}(z)\mathrm{d}s+\frac{1}{2} \|w(0)-z\|_{2}^{2}$$ $$=t\widehat{\mathcal{R}}(z)+\frac{1}{2}\|w(0)-z\|_{2}^{2}.$$

**Remark 7.6**: _("units" of GD and GF: \(t\) vs \(\frac{t}{\beta}\))_: Here's a back-of-the-envelope calculation to see why \(t\) becomes \(t/\beta\) and why they are really the same, and _not_ a sloppiness of the analysis.

* Suppose \(\|\nabla\widehat{\mathcal{R}}(w)\|\approx 1\) for sake of illustration.
* The "distance traveled" by GD is $$\|w_{t}-w_{0}\|=\|\frac{1}{\beta}\sum_{i}\nabla\widehat{\mathcal{R}}(w_{i})\| \leq\sum_{i}\frac{1}{\beta}\|\nabla\widehat{\mathcal{R}}(w_{i})\|\approx\frac{ t}{\beta}.$$
* The "distance traveled" by GF is (via Jensen) $$\|w(t)-w(0)\| =\|\int_{0}^{t}\nabla\widehat{\mathcal{R}}(w(s))\mathrm{d}s\|=\| \frac{1}{t}\int_{0}^{t}t\nabla\widehat{\mathcal{R}}(w(s))\mathrm{d}s\|$$ $$\leq\frac{1}{t}\int_{0}^{t}\|t\nabla\widehat{\mathcal{R}}(w(s))\| \mathrm{d}s\approx t.$$

**Remark 7.7**: _(potential functions)_:
* For critical points, the potential was \(\widehat{\mathcal{R}}(w(s))\) (or arguably \(\|\nabla\widehat{\mathcal{R}}(w(s))\|_{2}^{2}\)).
* Here, the potential was \(\|w(s)-z\|_{2}^{2}\). This particular choice is widespread in optimization. It is interesting since it is not part of the objective function; it's some gradient descent magic?

We can use similar objective functions with deep learning, without smoothness (!).

**Remark 7.8**: _(rates)_: Some rules of thumb (not comprehensive, and there are other ways).

* \(\frac{1}{t}\) is often a smoothness argument as above.
* \(\frac{1}{\sqrt{t}}\) uses Lipschitz (thus \(\|\nabla\widehat{\mathcal{R}}\|=\mathcal{O}(1)\)) in place of smoothness upper bound on \(\|\nabla\widehat{\mathcal{R}}\|\).
* \(\frac{1}{t^{2}}\) uses "acceleration," which is a fancy momentum inside the gradient.

* \(\exp(-{\cal O}(t))\) uses strong convexity (or other fine structure on \(\widehat{\cal R}\)).
* Stochasticity changes some rates and what is possible, but there are multiple settings and inconsistent terminology.

\(\underline{\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad \qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad \qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad \qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad \qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad \qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad \qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad \qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad \qquad\

**Remark 7.10** (stopping conditions): Say our goal is to find \(w\) so that \(\widehat{\mathcal{R}}(w)-\inf_{v}\widehat{\mathcal{R}}(v)\leq\epsilon\). When do we stop gradient descent?

* The \(\lambda\)-sc case is easy: by the preceding lemma, we know that we can stop when \(\|\nabla\widehat{\mathcal{R}}(w)\|\leq\sqrt{2\lambda\epsilon}\).
* Another easy case is when \(\inf_{v}\widehat{\mathcal{R}}(v)\) is known, and we just watch \(\widehat{\mathcal{R}}(w_{i})\). E.g., in classification tasks, deep networks are expect to get \(0\). For things like deep RL, once again it becomes a problem.
* Many software packages use heuristics. Some people just run their methods as long as possible. In convex cases, sometimes we can compute duality gaps.

**Remark 7.11** (Regularization and boundedness):

* Given \(\widehat{\mathcal{R}}_{\lambda}(w)=\widehat{\mathcal{R}}(w)+\lambda\|w\|^{2}/2\) with \(\widehat{\mathcal{R}}\geq 0\), optimal point \(\bar{w}\) satisfies $$\frac{\lambda}{2}\|\bar{w}\|_{2}^{2}\leq\widehat{\mathcal{R}}_{\lambda}( \bar{w})\leq\widehat{\mathcal{R}}_{\lambda}(0)=\widehat{\mathcal{R}}(0),$$ thus it suffices to search over bounded set \(\{w\in\mathbb{R}^{p}:\|w\|^{2}\leq 2\widehat{\mathcal{R}}(0)/\lambda\}\). This can often be plugged directly into generalization bounds.
* In deep learning, this style of regularization ("weight decay") is indeed used, but it isn't necessary for generalization, and is much smaller than what many generalization analyses suggest, and thus its overall role is unclear.

[ mjt(r): I should lemmas lemmas giving level set containment, and existence of minimizers.]

[ mjt(r): I should lemmas lemmas giving level set containment, and existence of minimizers.]

[ mjt(r): I should lemmas lemmas giving level set containment, and existence of minimizers.]

[ mjt(r): I should lemmas lemmas giving level set containment, and existence of minimizers.]

[ mjt(r): I should lemmas lemmas giving level set containment, and existence of minimizers.]

[ mjt(r): I should lemmas giving level set containment, and existence of minimizers.]

[ mjt(r): I should lemmas giving level set containment, and existence of minimizers.

For the second guarantee, expanding the square as usual,

$$\|w^{\prime}-\bar{w}\|^{2} =\|w-\bar{w}\|^{2}+\frac{2}{\beta}\left\langle\nabla\widehat{\mathcal{ R}}(w),\bar{w}-w\right\rangle+\frac{1}{\beta^{2}}\|\nabla\widehat{\mathcal{R}}(w) \|^{2}$$ $$\leq\|w-\bar{w}\|^{2}+\frac{2}{\beta}\left(\widehat{\mathcal{R}}( \bar{w})-\widehat{\mathcal{R}}(w)-\frac{\lambda}{2}\|\bar{w}-w\|_{2}^{2}\right)$$ $$\qquad+\frac{1}{\beta^{2}}\left(2\beta(\widehat{\mathcal{R}}(w)- \widehat{\mathcal{R}}(w^{\prime}))\right)$$ $$=(1-\lambda/\beta)\|w-\bar{w}\|^{2}+\frac{2}{\beta}\left(\widehat {\mathcal{R}}(\bar{w})-\widehat{\mathcal{R}}(w)+\widehat{\mathcal{R}}(w)- \widehat{\mathcal{R}}(w^{\prime})\right)$$ $$\leq(1-\lambda/\beta)\|w-\bar{w}\|^{2},$$

which gives the argument after a similar induction argument as before.

**Remark 7.12**:
* \(\beta/\lambda\) is sometimes called the _condition number_, based on linear system solvers, where it is \(\sigma_{\max}(X)/\sigma_{\min}(X)\) as in least squares. Note that \(\beta\geq\lambda\) and a good condition numbers improves these bounds.
* Setting the bounds to \(\epsilon\), it takes a linear number of iterations to learn a linear number of bits of \(\bar{w}\).
* Much of the analysis we've done goes through if the norm pair \((\|\cdot\|_{2},\|\cdot\|_{2})\) is replaced with \((\|\cdot\|,\|\cdot\|_{*})\) where the latter _dual norm_ is defined as $$\|s\|_{*}=\sup\left\{\langle s,w\rangle:\|w\|\leq 1\right\};$$ for instance, we can define \(\beta\)-smooth wrt \(\|\cdot\|\) as $$\|\nabla\widehat{\mathcal{R}}(w)-\nabla\widehat{\mathcal{R}}(w^{\prime})\|_{* }\leq\beta\|w-w^{\prime}\|.$$

Next let's handle the gradient flow.

**Theorem 7.6**: If \(\widehat{\mathcal{R}}\) is \(\lambda\)-sc, a minimum \(\bar{w}\) exists, and the GF \(w(t)\) satisfies

$$\|w(t)-\bar{w}\|^{2} \leq\|w(0)-\bar{w}\|^{2}\exp(-2\lambda t),$$ $$\widehat{\mathcal{R}}(w(t))-\widehat{\mathcal{R}}(\bar{w}) \leq\left(\widehat{\mathcal{R}}(w(0))-\widehat{\mathcal{R}}(\bar {w})\right)\exp(-2t\lambda).$$

**Proof.** By first-order optimality in the form \(\nabla\widehat{\mathcal{R}}(\bar{w})=0\), then

$$\frac{\mathrm{d}}{\mathrm{d}t}\frac{1}{2}\|w(t)-\bar{w}\|^{2} =\langle w(t)-\bar{w},\dot{w}(t)\rangle$$ $$=-\left\langle w(t)-\bar{w},\nabla\widehat{\mathcal{R}}(w(t))- \nabla\widehat{\mathcal{R}}(\bar{w})\right\rangle$$ $$\leq-\lambda\|w(t)-\bar{w}\|^{2}.$$

By Gronwall's inequality, this implies

$$\|w(t)-\bar{w}\|^{2} \leq\|w(0)-\bar{w}\|^{2}\exp\left(-\int_{0}^{t}2\lambda\mathrm{d}s\right)$$ $$\leq\|w(0)-\bar{w}\|^{2}\exp(-2\lambda t),$$which establishes the guarantee on distances to initialization. For the objective function guarantee,

$$\frac{\mathrm{d}}{\mathrm{d}t}(\widehat{\mathcal{R}}(w(t))-\widehat{ \mathcal{R}}(\bar{w})) =\left\langle\nabla\widehat{\mathcal{R}}(w(t)),\dot{w}(t)\right\rangle$$ $$=-\left\|\nabla\widehat{\mathcal{R}}(w(t))\right\|^{2}\leq-2 \lambda(\widehat{\mathcal{R}}(w(t))-\widehat{\mathcal{R}}(\bar{w})).$$

Gronwall's inequality implies

$$\widehat{\mathcal{R}}(w(t))-\widehat{\mathcal{R}}(\bar{w})\leq\left(\widehat{ \mathcal{R}}(w(0))-\widehat{\mathcal{R}}(\bar{w})\right)\exp(-2t\lambda).$$

**Remark 7.13**: As in all other rates proved for GF and GD, time \(t\) is replaced by "arc length units" \(t/\beta\).

We have strayed a little from our goals by producing laborious proofs that not only separate the objective function and the distances, but also require minimizers. Interestingly, we can resolve this by changing the step size to a large (seemingly worse?) one.

**Theorem 7.7**: Suppose \(\widehat{\mathcal{R}}\) is \(\beta\)-smooth and \(\lambda\)-sc, and a constant step size \(\frac{2}{\beta+\lambda}\). Then, for any \(z\),

$$\widehat{\mathcal{R}}(w_{t})-\widehat{\mathcal{R}}(z)+\frac{\lambda}{2}\|w_{t }-z\|^{2}\leq\left[\frac{\beta-\lambda}{\beta+\lambda}\right]^{t}\left(\widehat {\mathcal{R}}(w_{0})-\widehat{\mathcal{R}}(z)+\frac{\lambda}{2}\|w_{0}-z\|^{ 2}\right).$$

**Proof.** Homework problem \(\tilde{\backsim}\).

**Remark 7.14**: _(standard rates with strong convexity)_ Compared with standard proofs in the literature (Nesterov 2003, chap. 2), the preceding bound with step size \(2/(\beta+\lambda)\) is possibly loose: it seems possible to have a \(2t\) and not just \(t\) in the exponent, albeit after adjusting the other terms (and depending explicitly on minimizers). [ mjt(r): I need to resolve what's going on here...]

Moreover, another standard rate given in the literature is \(1/t\) under just strong convexity (no smoothness); however, this requires a step size \(\eta_{i}:=(\lambda(i+1))^{-1}\).

**7.9**: **Stochastic gradients**

Let's generalize gradient descent, and consider the iteration

$$w_{i+1}:=w_{i}-\eta_{i}g_{i},$$

where each \(g_{i}\) is merely some vector. If \(g_{i}:=\nabla\widehat{\mathcal{R}}(w_{i})\), then we have gradient descent, but in general we only approximate it. Later in this section, we'll explain how to make \(g_{i}\) a "stochastic gradient."

Our first step is to analyze this in our usual way with our favorite potential function, but accumulating a big error term: using convexity of \(\mathcal{R}\) and choosing a constant step size \(\eta_{i}:=\eta\geq 0\) for simplicity,

$$\|w_{i+1}-z\|^{2} =\|w_{i}-\eta g_{i}-z\|^{2}$$ $$=\|w_{i}-z\|^{2}-2\eta_{i}\left\langle g_{i},w_{i}-z\right\rangle +\eta^{2}\|g_{i}\|^{2}$$ $$=\|w_{i}-z\|^{2}+2\eta\left\langle g_{i}-\nabla\mathcal{R}(w_{i} )+\nabla\mathcal{R}(w_{i}),z-w_{i}\right\rangle+\eta^{2}\|g_{i}\|^{2}$$ $$\leq\|w_{i}-z\|^{2}+2\eta(\mathcal{R}(z)-\mathcal{R}(w_{i})+ \underbrace{\left\langle g_{i}-\nabla\mathcal{R}(w_{i}),z-w_{i}\right\rangle} _{\epsilon_{i}})+\eta^{2}\|g_{i}\|^{2},$$which after rearrangement gives

$$2\eta{\cal R}(w_{i})\leq 2\eta{\cal R}(z)+\|w_{i}-z\|^{2}-\|w_{i+1}-z\|^{2}+2 \eta\epsilon_{i}+\eta^{2}\|g_{i}\|^{2},$$

and applying \(\frac{1}{2\eta t}\sum_{i<t}\) to both sides gives

$$\frac{1}{t}\sum_{i<t}{\cal R}(w_{i})\leq{\cal R}(z)+\frac{\|w_{0}-z\|^{2}-\|w_ {t}-z\|^{2}}{2\eta t}+\frac{1}{t}\sum_{i<t}\left(\epsilon_{i}+\frac{\eta}{2}\| g_{i}\|^{2}\right).$$

The following lemma summarizes this derivation.

**Lemma 7.2**: Suppose \({\cal R}\) convex; set \(G:=\max_{i}\|g_{i}\|_{2}\), and \(\eta:=\frac{c}{\sqrt{t}}\). For any \(z\),

$${\cal R}\left(\frac{1}{t}\sum_{i<t}w_{i}\right)\leq\frac{1}{t}\sum_{i<t}{\cal R }(w_{i})\leq{\cal R}(z)+\frac{\|w_{0}-z\|^{2}}{2c\sqrt{t}}+\frac{cG^{2}}{2 \sqrt{t}}+\frac{1}{t}\sum_{i<t}\epsilon_{i}.$$

**Proof.** This follows from the earlier derivation after plugging in \(G\), \(\eta=c/\sqrt{t}\), and applying Jensen's inequality to the left hand side.

**Remark 7.15**:
* We get a bound on the averaged iterate or a minimum iterate, but not the last iterate! (We'll revisit this later.) Averaged iterates are often suggested in theory, but rare in applied classification (afaik), but I've heard of them used in deep RL; OTOH, averaging seems weird with nonconvexity?
* \(\eta=c/\sqrt{t}\) trades off between terms. If \(t\) not fixed in advance, can use \(\eta_{i}=c/\sqrt{1+i}\), but I'd rather shorten lecture a little by avoiding the needed algebra with non-constant step sizes, and for deep learning at least this style seems to not work well.
* This analysis works fine with \(\nabla{\cal R}(w_{i})\) replaced with subgradient \(s_{i}\in\partial{\cal R}(w_{i})\).
* Suppose \(\|\nabla{\cal R}(w_{i})\|\leq G\) and set \(D:=\max_{i}\|w_{i}-z\|\), then by Cauchy-Schwarz $$\frac{1}{t}\sum_{i<t}\epsilon_{i}\leq\frac{1}{t}\sum_{i<t}\left\langle g_{i}- \nabla{\cal R}(w_{i}),z-w_{i}\right\rangle\leq 2GD,$$ which does not go to \(0\) with \(t\)! Thus more structure needed on \(\epsilon_{i}\), this worst-case argument is bad.
* This proof easily handles projection to convex closed sets: replace \(w_{i}-\eta g_{i}\) with \(\Pi_{S}(w_{i}-\eta g_{i})\), and within the proof use the non-expansive property of \(\Pi_{S}\). This can be used to ensure that \(D\) up above is not too large. (We'll return to this point.)

Now let us define the standard stochastic gradient oracle:

$$\mathbb{E}[g_{i}|w_{\leq i}]=\nabla{\cal R}(w_{i}),$$

where \(w_{\leq i}\) signifies all randomness in \((w_{1},\ldots,w_{i})\).

**Remark 7.16**:
* We can't use an unconditional expectation because gradient at \(w_{i}\) should rely upon random variable \(w_{i}\)!* One way to satisfy this: sample \((x,y)\), and set \(g_{i}:=\ell^{\prime}(yf(x;w_{i}))y\nabla_{w}f(x;w_{i})\); conditioned on \(w_{\leq i}\), the only randomness is in \((x,y)\), and the conditional expectation is a gradient _over the distribution_!

Indeed, this setup allows the expectation to be nicely interpreted as an iterated integral over \((x_{1},y_{1})\), then \((x_{2},y_{2})\), and so on. The stochastic gradient \(g_{i}\) depends on \((x_{i},y_{i})\) and \(w_{i}\), but \(w_{i}\) does not depend on \((x_{i},y_{i})\), rather on \(((x_{j},y_{j}))_{j=1}^{i-1}\).

* It's standard to sample a _minibatch_ and average the \(g_{i}\) obtained from each, which ostensibly has the same conditional mean as \(g_{i}\), but improved variance. It can be hard to analyze this.
* Stochastic minibatch gradient descent is standard for deep networks. However, there is a delicate interplay between step size, minibatch size, and number of training epochs (Shallue et al. 2018).
* Annoyingly, there are many different settings for stochastic gradient descent, but they refer to themselves in the same way and it requires a closer look to determine the precise setting.
* Previous slide suggested \((x,y)\) is a fresh sample from the distribution; in this case, we are doing stochastic gradient descent on he population directly!
* We can also resample the training set, in which case \(\mathcal{R}\) is our usual empirical risk, and now the randomness is under our control (randomized algorithm, not random data from nature). The "SVRG/SDCA/SAG/etc" papers are in this setting, as are some newer SGD papers. Since people typically do multiple passes over the time, perhaps this setting makes sense.
* There are many deep learning papers that claim SGD does miraculous things to the optimization process. Unfortunately, none of these seem to come with a compelling and general theoretical analysis. Personally I don't know if SGD works further miracles (beyond computational benefits), but it's certainly interesting!

Now let's work towards our goal of showing that, with high probability, our stochastic gradient method does nearly as well as a regular gradient method. (We will not show any _benefit_ to stochastic noise, other than computation!)

Our main tool is as follows.

**Theorem 7.8**_(Azuma-Hoeffding)_** Suppose \((Z_{i})_{i=1}^{n}\) is a martingale difference sequence \((\mathbb{E}(Z_{i}|Z_{<i})=0)\) and \(\mathbb{E}\left|Z_{i}\right|\leq R\). Then with probability at least \(1-\delta\),

$$\sum_{i}Z_{i}\leq R\sqrt{2t\ln(1/\delta)}.$$

**Proof omitted,** though we'll sketch some approaches in a few weeks.

We will use this inequality to handle \(\sum_{i<t}\epsilon_{i}\). Firstly, we must show the desired expectations are zero. To start,

$$\mathbb{E}\left[\epsilon_{i}\ \Big{|}\ w_{\leq i}\right] =\mathbb{E}\left[\left\langle g_{i}-\nabla\mathcal{R}(w_{i}),z-w_{i }\right\rangle\ \Big{|}\ w_{\leq i}\right]$$ $$=\left\langle\mathbb{E}\left[g_{i}-\nabla\mathcal{R}(w_{i})\ \Big{|}\ w_{\leq i}\right],z-w_{i}\right\rangle$$ $$=\left\langle 0,z-w_{i}\right\rangle$$ $$=0.$$

Next, by Cauchy-Schwarz and the triangle inequality,

$$\mathbb{E}\left|\epsilon_{i}\right|=\mathbb{E}\left|\left\langle g_{i}-\nabla \widehat{\mathcal{R}}(w_{i}),w_{i}-z\right\rangle\right|\leq\mathbb{E}\left( \|g_{i}\|+\|\nabla\widehat{\mathcal{R}}(w_{i})\|\right)\|w_{i}-z\|\leq 2GD.$$

Consequently, by Azuma-Hoeffding, with probability at least \(1-\delta\),

$$\sum_{i}\epsilon_{i}\leq 2GD\sqrt{2t\ln(1/\delta)}.$$

Plugging this into the earlier approximate gradient lemma gives the following. [ mjt(r): should give explicit cref]

**Lemma 7.3**: Suppose \(\mathcal{R}\) convex; set \(G:=\max_{i}\|g_{i}\|_{2}\), and \(\eta:=\frac{1}{\sqrt{t}}\), \(D\geq\max_{i}\|w_{i}-z\|\), and suppose \(g_{i}\) is a stochastic gradient at time \(i\). With probability at least \(1-\delta\),

$$\mathcal{R}\left(\frac{1}{t}\sum_{i<t}w_{i}\right) \leq\frac{1}{t}\sum_{i<t}\mathcal{R}(w_{i})$$ $$\leq\mathcal{R}(z)+\frac{D^{2}}{2\sqrt{t}}+\frac{G^{2}}{2\sqrt{t}} +\frac{2DG\sqrt{2\ln(1/\delta)}}{\sqrt{t}}.$$

**Remark 7.17**:
* If we tune \(\eta=c/\sqrt{t}\) here, we only get a \(DG\) term. [ mjt(r): I should do it]
* We can ensure \(D\) is small by projecting to a small set each iteration. By the contractive property of projections, the analysis still goes through.
* By the tower property of conditional expectation, meaning \(\mathbb{E}=\mathbb{E}\,\mathbb{E}[\cdot|w_{\leq i}]\), without Azuma-Hoeffding we easily get a bound on the expected average error: $$\mathbb{E}\left[\frac{1}{t}\sum_{i<t}\mathcal{R}(w_{i})\right]\leq\mathcal{R} (z)+\frac{\|w_{0}-z\|^{2}}{2\sqrt{t}}+\frac{G^{2}}{2\sqrt{t}}.$$
* If the preceding bound in expectation is sufficient, expected is enough, a more careful analysis lets us use the last iterate (Shamir and Zhang 2013); AFAIK a high probability version still doesn't exist.
* The Martingale structure is delicate: if we re-use even a single data-point, then we can't treat \(\mathcal{R}\) as the population risk, but instead as the empirical risk. [ mjt(r): and here my notation is truly frustrating.]
* In practice, randomly sampling a permutation over the training data at the beginning of each epoch is common; it can be hard to analyze.

* **Why SGD in ML?** In statistical problems, we shouldn't expect test error better than \(\frac{1}{\sqrt{n}}\) or \(\frac{1}{n}\) anyway, so we shouldn't optimize to crazy accuracy. With SGD, the per-iteration cost is low. Meanwhile, heavyweight solvers like Newton methods require a massive per-iteration complexity, with the promise of crazy accuracy; but, again we don't need that crazy accuracy here. [ mjt(r): summarize as "computation."]

## 8 Two NTK-based optimization proofs near initializatikon

Here we will show our first optimization guarantees for (shallow) networks: one based on strong convexity, and one based on smoothness.

**under construction.**

[style=unboxed,leftmargin=0cm,rightmargin=0cm,topsep=0cm,itemsep=0cm,parsep=0cm,topsep=0cm,partopsep=0cm,label=**8.1**] Strong convexity style NTK optimization proof (include preamble saying this looks like + **theoremisc_smooth?**){.mjt} Theorem 7.5

**Finally** we will prove (rather than assert) that we can stay close to initialization long enough to get a small risk with an analysis that is essentially convex, essentially following the NTK (Taylor approximation).

* This proof is a simplification of one by Chizat and Bach (2019). There are enough differences that it's worth checking the original.
* That paper highlights a "scaling phenomenon" as an explanation of the NTK. Essentially, increasing with always decreases initialization variance, and the paper argues this corresponds to "zooming in" on the Taylor expansion in function space, and flattening the dynamics.
* This "scaling perspective" pervades much of the NTK literature and I recommend looking at (Chizat and Bach, 2019) for further discussion; I do not discuss it much in this course or even in this proof, though I keep Chizat's \(\alpha>0\) scale parameter.
* This proof comes after many earlier NTK analyses, e.g., (Jacot, Gabriel, and Hongler, 2018; Simon S. Du et al., 2018; Allen-Zhu, Li, and Liang, 2018; Arora, Du, Hu, Li, and Wang, 2019). I like the proof by (Chizat and Bach, 2019) very much and learned a lot from it; it was the most natural for me to teach. OTOH, it is quite abstract, and we'll need homework problems to boil it down further.

**Basic notation.** For convenience, bake the training set into the predictor:

$$f(w):=\begin{bmatrix}f(x_{1};w)\\ \vdots\\ f(x_{n};w)\end{bmatrix}\in\mathbb{R}^{n}.$$

We'll be considering squared loss regression:

$$\widehat{\mathcal{R}}(\alpha f(w)):=\frac{1}{2}\|\alpha f(w)-y\|^{2},\qquad \widehat{\mathcal{R}}_{0}:=\widehat{\mathcal{R}}(\alpha f(w(0))),$$

where \(\alpha>0\) is a scale factor we'll optimize later. [ mjt(r): maybe I should use \(\mathcal{L}\) not \(\widehat{\mathcal{R}}\) since unnormalized.]We'll consider gradient flow:

$$\dot{w}(t) :=-\nabla_{w}\widehat{\mathcal{R}}(\alpha f(w(t)))=-\alpha J_{t}^{ \intercal}\nabla\widehat{\mathcal{R}}(\alpha f(w(t))),$$ $$\text{where }J_{t}:=J_{w(t)} :=\begin{bmatrix}\nabla f(x_{1};w(t))^{\top}\\ \vdots\\ \nabla f(x_{n};w(t))^{\top}\end{bmatrix}\in\mathbb{R}^{n\times p}.$$

We will also explicitly define and track a flow \(u(t)\) over the tangent model; what we care about is \(w(t)\), but we will show that indeed \(u(t)\) and \(w(t)\) stay close in this setting. (Note that \(u(t)\) is _not_ needed for the analysis of \(w(t)\).)

$$f_{0}(u) :=f(w(0))+J_{0}(u-w(0)).$$ $$\dot{u}(t) :=-\nabla_{u}\widehat{\mathcal{R}}(\alpha f_{0}(u(t)))=-\alpha J_ {0}^{\intercal}\nabla\widehat{\mathcal{R}}(\alpha f_{0}(u(t))).$$

Both gradient flows have the same initial condition:

$$u(0)=w(0),\qquad f_{0}(u(0))=f_{0}(w(0))=f(w(0)).$$

**Remark 8.1** (_initialization, width, etc_):
* Notice that the setup so far doesn't make any mention of width, neural networks, random initialization, etc.! It's all abstracted away! This is good and bad: the good is that it highlights the "scale" phenomenon, as \(\alpha\) is the only concretely interpretable parameter here. On the downside, we need to do some work to get statements about width etc.

**Assumptions.**:

$$\begin{split}\operatorname{rank}(J_{0})&=n,\\ \sigma_{\min}&:=\sigma_{\min}(J_{0})=\sqrt{\lambda_{ \min}(J_{0}J_{0}^{\intercal})}=\sqrt{\lambda_{n}(J_{0}J_{0}^{\intercal})}>0,\\ \sigma_{\max}&:=\sigma_{\max}(J_{0})>0,\\ \|J_{w}-J_{v}\|&\leq\beta\|w-v\|.\end{split} \tag{4}$$

**Remark 8.2** (\(J_{0}J_{0}^{\intercal}\) has full rank, a "representation assumption"): _This is a "representation assumption" in an explicit sense: it implies the tangent model has exact solutions to the least squares problem, regardless of the choice of \(y\), meaning the training error can always be made \(0\). In detail, consider the least squares problem solved by the tangent space:_

$$\min_{u\in\mathbb{R}^{p}}\frac{1}{2}\left\|f_{0}(u)-y\right\|^{2}=\min_{u\in \mathbb{R}^{p}}\frac{1}{2}\left\|J_{0}u-y_{0}\right\|^{2},$$

_where we have chosen \(y_{0}:=y+J_{0}w(0)-f(w(0))\) for convenience. The normal equations for this least squares problem are_

$$J_{0}^{\intercal}J_{0}u=J_{0}^{\intercal}y_{0}.$$

_Let \(J_{0}=\sum_{i=1}^{n}s_{i}u_{i}v_{i}^{\intercal}\) denote the SVD of \(J_{0}\), which has \(n\) terms by the rank assumption; the corresponding pseudoinverse is \(J_{0}^{\dagger}=\sum_{i=1}^{n}s_{i}^{-1}v_{i}u_{i}^{\intercal}\). Multiplying both sides by \((J_{0}^{\dagger})^{\intercal}\),_

$$J_{0}u=(J_{0}^{\dagger})^{\intercal}J_{0}^{\intercal}J_{0}u=(J_{0}^{\dagger}) ^{\intercal}J_{0}^{\intercal}y_{0}=\left[\sum_{i=1}^{n}u_{i}u_{i}^{\intercal} \right]y_{0}=y_{0},$$where the last step follows since \([\sum_{i}u_{i}u_{i}^{\mathsf{ T}}]\) is idempotent and full rank, and therefore the identity matrix. In particular, we can choose \(\hat{u}=J_{0}^{\dagger}y_{0}\), then \(J_{0}\hat{u}=[\sum_{i}u_{i}u_{i}^{\mathsf{ T}}]y_{0}=y_{0}\), and in particular $$\frac{1}{2}\left\|f_{0}(\hat{u})-y\right\|^{2}=\frac{1}{2}\left\|J_{0}\hat{u}-y _{0}\right\|^{2}=0.$$ As such, the full rank assumption is explicitly a representation assumption: we are forcing the tangent space least squares problem to always have solutions.

**Theorem 8.1** (see also (Theorem 3.2, Chizat and Bach 2019)): _Assume eq. 4 and \(\alpha\geq\frac{\beta\sqrt{1152\sigma_{\mathrm{max}}^{2}\widehat{\mathcal{R}}_{0 }}}{\sigma_{\mathrm{min}}^{2}}\). Then_

$$\max\left\{\widehat{\mathcal{R}}(\alpha f(w(t))),\widehat{ \mathcal{R}}(\alpha f_{0}(u(t)))\right\} \leq\widehat{\mathcal{R}}_{0}\exp(-t\alpha^{2}\sigma_{\mathrm{ min}}^{2}/2),$$ $$\max\left\{\|w(t)-w(0)\|,\|u(t)-w(0)\|\right\} \leq\frac{3\sqrt{8\sigma_{\mathrm{max}}^{2}\widehat{\mathcal{R}}_{0 }}}{\alpha\sigma_{\mathrm{min}}^{2}}.$$

**Remark 8.3** (shallow case): To get a handle on the various abstract constants and what they mean, consider the shallow case, namely \(f(x;w)=\sum_{j}s_{j}\sigma(w_{j}^{\mathsf{ T}}x)\), where \(s_{j}\in\{\pm 1\}\) is not trained, and each \(w_{j}\) is trained.

**Smoothness constant.** Let \(X\in\mathbb{R}^{n\times d}\) be a matrix with the \(n\) training inputs as rows, and suppose \(\sigma\) is \(\beta_{0}\)-smooth. Then

$$\|J_{w}-J_{v}\|_{2}^{2} =\sum_{i,j}\|x_{i}\|^{2}(\sigma^{\prime}(w_{j}^{\mathsf{ T}}x_{i})-\sigma^{\prime}(v_{j}^{\mathsf{ T}}x_{i}))^{2}$$ $$\leq\sum_{i,j}\|x_{i}\|^{4}\beta_{0}^{2}\|w_{j}-v_{j}\|^{2}$$ $$=\beta_{0}^{2}\|X\|_{\mathrm{F}}^{4}\|w-v\|^{2}.$$

Thus \(\beta=\beta_{0}\|X\|_{\mathrm{F}}^{2}\) suffices, which we can ballpark as \(\beta=\Theta(n)\).

**Singular values.** Now that we have an interpretation of the full rank assumption, ballpark the eigenvalues of \(J_{0}J_{0}^{\mathsf{ T}}\). By definition,

$$(J_{0}J_{0}^{\mathsf{ T}})_{i,j}=\nabla f(x_{i};w(0))^{\mathsf{ T}}\nabla f(x_{j};w(0)).$$

Holding \(i\) fixed and letting \(j\) vary, we can view the corresponding column of \((J_{0}J_{0}^{\mathsf{ T}})\) as another feature representation, and \(\operatorname{rank}(J_{0})=n\) means none of these examples, in this feature representation, are linear combinations of others. This gives a concrete sense under which these eigenvalue assumptions are _representation assumptions_.

Now suppose each \(w_{j}(0)\) is an iid copy of some random variable \(v\). Then, by definition of \(J_{0}\),

$$\operatorname*{\mathbb{E}}_{w(0)}(J_{0}J_{0}^{\mathsf{ T}})_{i,j} =\operatorname*{\mathbb{E}}_{w(0)}\nabla f(x_{i};w(0))^{\mathsf{ T}}\nabla f(x_{j};w(0)).$$ $$=\operatorname*{\mathbb{E}}_{w(0)}\sum_{k}s_{k}^{2}\sigma^{ \prime}(w_{k}(0)^{\mathsf{ T}}x_{i})\sigma^{\prime}(w_{k}(0)^{\mathsf{ T}}x_{j})x_{i}^{\mathsf{ T}}x_{j}$$ $$=m\operatorname*{\mathbb{E}}_{v}\sigma^{\prime}(v^{\mathsf{ T}}x_{i})\sigma^{\prime}(v^{\mathsf{ T}}x_{j})x_{i}^{\mathsf{ T}}x_{j}.$$

In other words, it seems reasonable to expect \(\sigma_{\mathrm{min}}\) and \(\sigma_{\mathrm{max}}\) to scale with \(\sqrt{m}\).

**Initial risk \(\widehat{\mathcal{R}}_{0}\).** Let's consider two different random initializations.

In the first case, we use one of the fancy schemes we mentioned to force \(f(w(0))=0\); e.g., we can make sure that \(s_{j}\) is positive and negative an equal number of times, then sample \(w_{j}\) for \(s_{j}=+1\), and then make \(w_{j}\) for \(s_{j}=-1\) be the negation. With this choice, \(\widehat{\mathcal{R}}_{0}=\|y\|^{2}/2=\Theta(n)\).

On the other hand, if we do a general random initialization of both \(s_{j}\) and \(w_{j}\), then we can expect enough cancellation that, roughly, \(f(x_{i};w(0))=\Theta(\sqrt{m})\) (assuming \(w_{j}\)'s variance is a constant and not depending on \(m\): that would defeat the purpose of separating out the scale parameter \(\alpha\)). then \(\|\alpha f(w(0))\|^{2}=\Theta(\alpha^{2}mn)\), and \(\widehat{\mathcal{R}}_{0}=\Theta(\alpha^{2}mn)\), and thus the lower bound condition on \(\alpha\) will need to be checked carefully.

**Combining all parameters.** Again let's split into two cases, based on the initialization as discussed immediately above.

* **The case \(\widehat{\mathcal{R}}_{0}=\Theta(\alpha^{2}nm)\).** Using \(\beta=\Theta(n)\), the condition on \(\alpha\) indeed has \(\alpha\) on both sides, and becomes $$\sigma_{\min}^{3}\geq\Omega(\beta\sigma_{\max}\sqrt{nm})=\sigma_{\max}\Omega( \sqrt{mn^{3}}).$$ Since we said the singular values are of order \(\sqrt{m}\), we get roughly \(m^{3/2}\geq\sqrt{m^{2}n^{3}}\), thus \(m\geq n^{3}\). Since the lower bound on \(\alpha\) turned into a lower bound on \(m\), let's plug this \(\widehat{\mathcal{R}}_{0}\) into the rates to see how they simplify: $$\max\left\{\widehat{\mathcal{R}}(\alpha f(w(t))),\widehat{\mathcal{ R}}(\alpha f_{0}(u(t)))\right\} \leq\widehat{\mathcal{R}}_{0}\exp\left(-\frac{t\alpha^{2}\sigma_{ \min}^{2}}{2}\right)$$ $$=\mathcal{O}\left(\alpha^{2}nm\exp\left(-\frac{t\alpha^{2}\sigma_ {\min}^{2}}{2}\right)\right),$$ $$\max\left\{\|w(t)-w(0)\|,\|u(t)-w(0)\|\right\} \leq\frac{3\sqrt{8\sigma_{\max}^{2}\widehat{\mathcal{R}}_{0}}}{ \alpha\sigma_{\min}^{2}}$$ $$=\mathcal{O}\left(\frac{\sqrt{\sigma_{\max}^{2}nm}}{\sigma_{\min }^{2}}\right).$$ In these inequalities, the distance to initialization is not affected by \(\alpha\): this makes sense, as the key work needed by the gradient flow is to clear the initial noise so that \(y\) can be fit exactly. Meanwhile, the empirical risk rate does depend on \(\alpha\), and is dominated by the exponential term, suggesting that \(\alpha\) should be made arbitrarily large. There is indeed a catch limiting the reasonable choices of \(\alpha\), as will be pointed out shortly. For now, to pick a value which makes the bounds more familiar, choose \(\alpha=\hat{\alpha}:=1/\sigma_{\max}\), whereby additionally simplifying via \(\sigma_{\min}\) and \(\sigma_{\max}\) being \(\Theta(\sqrt{m})\) gives $$\max\left\{\widehat{\mathcal{R}}(\alpha f(w(t))),\widehat{\mathcal{ R}}(\alpha f_{0}(u(t)))\right\} =\mathcal{O}\left(\sigma_{\max}^{-2}nm\exp\left(-\frac{t\sigma_{ \min}^{2}}{2\sigma_{\max}^{2}}\right)\right)$$ $$=\mathcal{O}\left(n\exp\left(-\frac{t\sigma_{\min}^{2}}{2\sigma_ {\max}^{2}}\right)\right),$$ $$\max\left\{\|w(t)-w(0)\|,\|u(t)-w(0)\|\right\} =\mathcal{O}\left(\frac{\sqrt{\sigma_{\max}^{2}nm}}{\sigma_{\min }^{2}}\right)=\mathcal{O}\left(\sqrt{n}\right).$$Written this way, the empirical risk rate depends on the _condition number_\(\sigma_{\max}/\sigma_{\min}\) of the NTK Gram matrix, which is reminiscent of the purely strongly convex and smooth analyses as in Theorem 7.5.
* **The case \(\widehat{\mathcal{R}}_{0}=\Theta(n)\).** Using \(\beta=\Theta(n)\), the condition on \(\alpha\) becomes $$\alpha=\Omega\left(\frac{\beta\sqrt{\sigma_{\max}^{2}\widehat{\mathcal{R}}_{0 }}}{\sigma_{\min}^{3}}\right)=\Omega\left(\frac{\sigma_{\max}n^{3/2}}{\sigma_{ \min}^{3}}\right).$$ We have removed the cancelation from the previous case, and are now constrained in our choice of \(\alpha\); we can still set \(\alpha:=1/\sigma_{\max}\), which after using our estimate of \(\sqrt{m}\) for \(\sigma_{\min}\) and \(\sigma_{\max}\) get a similar requirement \(m=\Omega(n^{3})\). More generally, we get \(\alpha=\Omega(n^{3/2}/m)\), which means for large enough \(m\) we can treat as close to \(1/m\). [ \(\,\)mjt(c): Frederic Koehler points out that the first case can still look like \(\widetilde{\mathcal{R}}_{0}=\Theta(\alpha^{2}mn+n)\) and even \(\Theta(n)\) when \(\alpha\) is small; I need to update this story.]

**Possible values of \(\alpha\).** The two preceding cases considered lower bounds on \(\alpha\). In the case \(\widehat{\mathcal{R}}_{0}=\Theta(\alpha^{2}nm)\), it even seemed that we can make \(\alpha\) whatever we want; in either case, the time required to make \(\widetilde{\mathcal{R}}(\alpha f(w(t)))\) small will decrease as \(\alpha\) increases, so why not simply make \(\alpha\) arbitrarily large?

An issue occurs once we perform time discretization. Below, we will see that the smoothness of the model looks like \(\alpha^{2}\sigma_{\max}^{2}\) near initialization; as such, a time discretization, using tools such as in Theorem 7.3, will require a step size roughly \(1/(\alpha^{2}\sigma_{\max}^{2})\), and in particular while we may increase \(\alpha\) to force the gradient flow to seemingly converge faster, a smoothness-based time discretization will need the same number of steps.

As such, \(\alpha=1/\sigma_{\max}\) seems a reasonable way to simplify many terms in this shallow setup, which translates into a familiar \(1/\sqrt{m}\) NTK scaling.

**Proof of Theorem 8.1.**

* First we choose a fortuitous radius \(B:=\frac{\sigma_{\min}}{2\beta}\), and seek to study the properties of weight vectors \(w\) which are \(B\)-close to initialization: $$\|w-w(0)\|\leq B;$$ This \(B\) will be chosen to ensure \(J_{t}\) and \(J_{0}\) are close, amongst other things. Moreover, we choose a \(T\) so that all \(t\in[0,T]\) are in this good regime: $$T:=\inf\left\{t\geq 0:\|w(t)-w(0)\|>B\right\}.$$
* Now consider any \(t\in[0,T]\). [ \(\,\)mjt(c): i should include explicit lemma pointers for each.]
* First we show that if \(J_{t}J_{t}^{\mathrm{T}}\) is positive definite, then we rapidly decrease risk, essentially following our old strong convexity proof.
* Next, since the gradient of the least squares risk is the residual, then decreasing risk implies decreasing gradient norms, and in particular we can not travel far.
* The above steps go through directly for \(u(t)\) due to the positive definiteness of \(J_{0}J_{0}^{\mathrm{T}}\); by the choice of \(B\), we can also prove they hold for \(J_{t}J_{t}^{\mathrm{T}}\).
* As a consequence we also immediately get that we never escape this ball: the gradient norms decay sufficiently rapidly. Consequently, \(T=\infty\), and we don't need conditions on \(t\) in the theorem!

**Remark 8.4**: That is to say, in this setting, \(\alpha\) large enough (\(m\) large enough in the shallow case) ensure we stay in the NTK regime forever! This is _not_ the general case.

The evolution in prediction space is

$$\frac{\mathrm{d}}{\mathrm{d}t}\alpha f(w(t)) =\alpha J_{t}\dot{w}(t)=-\alpha^{2}J_{t}J_{t}^{\mathsf{T}}\nabla \widehat{\mathcal{R}}(\alpha f(w(t))),$$ $$=-\alpha^{2}J_{t}J_{t}^{\mathsf{T}}(\alpha f(w(t))-y),$$ $$\frac{\mathrm{d}}{\mathrm{d}t}\alpha f_{0}(u(t)) =\frac{\mathrm{d}}{\mathrm{d}t}\alpha\left(f(w(0)+J_{0}(u(t)-w(0) )\right)=\alpha J_{0}\dot{u}(t)$$ $$=-\alpha^{2}J_{0}J_{0}^{\mathsf{T}}\nabla\widehat{\mathcal{R}}( \alpha f_{0}(u(t)))$$ $$=-\alpha^{2}J_{0}J_{0}^{\mathsf{T}}(\alpha f_{0}(u(t))-y).$$

The first one is complicated because we don't know how \(J_{t}\) evolves.

But the second one can be written

$$\frac{\mathrm{d}}{\mathrm{d}t}\left[\alpha f_{0}(u(t))\right]=-\alpha^{2}\left( J_{0}J_{0}^{\mathsf{T}}\right)\left[\alpha f_{0}(u(t))\right]+\alpha^{2}\left(J_{0}J _{0}^{\mathsf{T}}\right)y,$$

which is a concave quadratic _in the predictions \(\alpha f_{0}(u(t))\)_.

**Remark 8.5**: The original NTK paper, (Jacot, Gabriel, and Hongler 2018), had as its story that GF follows a gradient in kernel space. Seeing the evolution of \(\alpha f_{0}(u(t))\) makes this clear, as it is governed by \(J_{0}J_{0}^{\mathsf{T}}\), the Gram or kernel matrix!

Let's fantasize a little and suppose \((J_{w}J_{w})^{\mathsf{T}}\) is also positive semi-definite. Do we still have a nice convergence theory?

**Lemma 8.1**: Suppose \(\dot{z}(t)=-Q(t)\nabla\widehat{\mathcal{R}}(z(t))\) and \(\lambda:=\inf_{t\in[0,\tau]}\lambda_{\min}Q(t)>0\). Then for any \(t\in[0,\tau]\),

$$\widehat{\mathcal{R}}(z(t))\leq\widehat{\mathcal{R}}(z(0))\exp(-2t\lambda).$$

**Remark 8.6**: A useful consequence is

$$\|z(t)-y\|=\sqrt{2\widehat{\mathcal{R}}(z(t))}\leq\sqrt{2\widehat{\mathcal{R} }(z(0))\exp(-2t\lambda)}=\|z(0)-y\|\exp(-t\lambda).$$

**Proof.** Mostly just repeating our old strong convexity steps,

$$\frac{\mathrm{d}}{\mathrm{d}t}\frac{1}{2}\|z(t)-y\|^{2} =\left\langle-Q(t)(z(t)-y),z(t)-y\right\rangle$$ $$\leq-\lambda_{\min}\left(Q(t)\right)\left\langle z(t)-y,z(t)-y\right\rangle$$ $$\leq-2\lambda\|z(t)-y\|^{2}/2,$$

and Gronwall's inequality completes the proof.

We can also prove this setting implies we stay close to initialization.

**Lemma 8.2**: Suppose \(\dot{v}(t)=-S(t)^{\top}\nabla\widehat{\mathcal{R}}(g(v(t)))\), where \(S_{t}S_{t}^{\mathrm{ T}}=Q_{t}\), and \(\lambda_{i}(Q_{t})\in[\lambda,\lambda_{1}]\) for \([0,\tau]\). Then for \(t\in[0,\tau]\),

$$\|v(t)-v(0)\|\leq\frac{\sqrt{\lambda_{1}}}{\lambda}\|g(v(0))-y\|\leq\frac{ \sqrt{2\lambda_{1}\widehat{\mathcal{R}}(g(v(0)))}}{\lambda}.$$

**Proof.**

$$\|v(t)-v(0)\| =\left\|\int_{0}^{t}\dot{v}(s)\mathrm{d}s\right\|\leq\int_{0}^{t} \|\dot{v}(s)\|\mathrm{d}s$$ $$=\int_{0}^{t}\|S_{t}^{\mathrm{ T}}\nabla\mathcal{R}(g(v(s)))\|\mathrm{d}s$$ $$\leq\sqrt{\lambda_{1}}\int_{0}^{t}\|g(v(s))-y\|\mathrm{d}s$$ $$\stackrel{{(*)}}{{\leq}}\sqrt{\lambda_{1}}\|g(v(0) )-y\|\int_{0}^{t}\exp(-s\lambda)\mathrm{d}s$$ $$\leq\frac{\sqrt{\lambda_{1}}}{\lambda}\|g(v(0))-y\|$$ $$\leq\frac{\sqrt{2\lambda_{1}\widehat{\mathcal{R}}(g(v(0)))}}{\lambda},$$

where \((*)\) used \(+\)Lemma 8.1.

**Where does this leave us?**

We can apply the previous two lemmas to the _tangent model_\(u(t)\), since for any \(t\geq 0\),

$$\dot{u}(t)=-\alpha J_{0}^{\mathrm{ T}}\nabla\widehat{\mathcal{R}}(\alpha f_{0}(u(t))),\quad\frac{\mathrm{d}}{ \mathrm{d}t}\alpha f_{0}(u(t))=-\alpha^{2}(J_{0}J_{0}^{\mathrm{ T}})\nabla\widehat{\mathcal{R}}(\alpha f_{0}(u(t))).$$

Thus since \(Q_{0}:=\alpha^{2}J_{0}J_{0}^{\mathrm{ T}}\) satisfies \(\lambda_{i}(Q_{0})\in\alpha^{2}[\sigma_{\min}^{2},\sigma_{\max}^{2}]\),

$$\widehat{\mathcal{R}}(\alpha f_{0}(u(t))) \leq\widehat{\mathcal{R}}_{0}\exp(-2t\alpha^{2}\sigma_{\min}^{2}),$$ $$\|u(t)-u(0)\| \leq\frac{\sqrt{2\sigma_{\max}^{2}\widehat{\mathcal{R}}_{0}}}{ \alpha\sigma_{\min}^{2}}.$$

How about \(w(t)\)?

Let's relate \((J_{w}J_{w}^{\mathrm{ T}})\) to \((J_{0}J_{0}^{\mathrm{ T}})\).

**Lemma 8.3**: Suppose \(\|w-w(0)\|\leq B=\frac{\sigma_{\min}}{2\beta}\). Then

$$\sigma_{\min}(J_{w}) \geq\sigma_{\min}-\beta\|w-w(0)\|_{2}\geq\frac{\sigma_{\min}}{2},$$ $$\sigma_{\max}(J_{w}) \leq\frac{3\sigma_{\max}}{2}.$$

**Proof.** For the upper bound,

$$\|J_{w}\|\leq\|J_{0}\|+\|J_{w}-J_{0}\|\leq\|J_{0}\|+\beta\|w-w(0)\|\leq\sigma_ {\max}+\beta B=\sigma_{\max}+\frac{\sigma_{\min}}{2}.$$For the lower bound, given vector \(v\) define \(A_{v}:=J_{0}^{\intercal}v\) and \(B_{v}:=(J_{w}-J_{0})^{\intercal}v\), whereby

$$\|A_{v}\|\geq\sigma_{\min}\|v\|,\qquad\|B_{v}\|\leq\|J_{w}-J_{0}\|\cdot\|v\|\leq \beta B\|v\|,$$

and thus

$$\sigma_{\min}(J_{w})^{2} =\min_{\|v\|=1}v^{\intercal}J_{w}J_{w}^{\intercal}v$$ $$=\min_{\|v\|=1}\left((J_{0}+J_{w}-J_{0})^{\intercal}v\right)^{ \intercal}(J_{0}+J_{w}-J_{0})^{\intercal}v$$ $$=\min_{\|v\|=1}\|A_{v}\|^{2}+2A_{v}^{\intercal}B_{v}+\|B_{v}\|^{2}$$ $$\geq\min_{\|v\|=1}\|A_{v}\|^{2}-2\|A_{v}\|\cdot\|B_{v}\|+\|B_{v} \|^{2}$$ $$=\min_{\|v\|=1}\left(\|A_{v}\|-\|B_{v}\|\right)^{2}\geq\min_{\|v \|=1}\left(\sigma_{\min}-\beta B\right)^{2}\|v\|^{2}=\left(\frac{\sigma_{\min} }{2}\right)^{2}.$$

Using this, for \(t\in[0,T]\),

$$\dot{w}(t)=-\alpha J_{w}^{\intercal}\nabla\widehat{\mathcal{R}}(\alpha f(w(t))),\quad\frac{\mathrm{d}}{\mathrm{d}t}\alpha f(w(t))=-\alpha^{2}(J_{w}J_{w}^{ \intercal})\nabla\widehat{\mathcal{R}}(\alpha f(w(t))).$$

Thus since \(Q_{t}:=\alpha^{2}J_{t}J_{t}^{\intercal}\) satisfies \(\lambda_{i}(Q_{t})\in\alpha^{2}[\sigma_{\min}^{2}/4,9\sigma_{\max}^{2}/4]\),

$$\widehat{\mathcal{R}}(\alpha f(w(t))) \leq\widehat{\mathcal{R}}_{0}\exp(-t\alpha^{2}\sigma_{\min}^{2}/2),$$ $$\|w(t)-w(0)\| \leq\frac{3\sqrt{8\sigma_{\max}^{2}\widehat{\mathcal{R}}_{0}}}{ \alpha\sigma_{\min}^{2}}=:B^{\prime}.$$

It remains to show that \(T=\infty\). Invoke, for the first time, the assumed lower bound on \(\alpha\), namely

$$\alpha\geq\frac{\beta\sqrt{1152\sigma_{\max}^{2}\widehat{\mathcal{R}}_{0}}}{ \sigma_{\min}^{3}},$$

which by the above implies then \(B^{\prime}\leq\frac{B}{2}\). Suppose contradictorily that \(T<\infty\); since \(t\mapsto w(t)\) is continuous, then \(t\mapsto\|w(t)-w(0)\|\) is also continuous and starts from \(0\), and therefore \(\|w(T)-w(0)\|=B>0\) exactly. But due to the lower bound on \(\alpha\), we also have \(\|w(T)-w(0)\|\leq\frac{B}{2}<B\), a contradiction.

This completes the proof. \(\dots\):

**Remark 8.7** (_retrospective_):
* On the downside, the proof is not only _insensitive_ to benefits of \(w(t)\) over \(u(t)\), moreover the guarantees on \(w(t)\) are a _degradation_ of those on \(u(t)\)! That is to say, this proof does not demonstrate any benefit to the nonlinear model over the linear one.
* Note that \(w(t)\) and \(u(t)\) are close by triangle inequality: $$\|w(t)-u(t)\| \leq\|w(t)-w(0)\|+\|u(t)-w(0)\|,$$ $$\|\alpha f(w(t))-\alpha f_{0}(u(t))\| \leq\|\alpha f(w(t))-y\|+\|\alpha f_{0}(u(t))-y\|.$$

[ mjt(r): I should move this earlier. Somewhere I should also mention that ideally we'd have a \(\|w^{\intercal}\|_{2,\infty}\) bound, but this proof is architecture agnostic so it wouldn't be natural.]

**Theorem 7.3**: _Let \(\widehat{\mathcal{R}}\) be a locally Lipschitz domain and \(\widehat{\mathcal{R}}\) be a locally Lipschitz domain. Then \(\widehat{\mathcal{R}}\) is locally Lipschitz._

[MISSING_PAGE_POST]

**Proof.** Let \(\widehat{\mathcal{R}}\) be a locally Lipschitz domain.

If \(R\) satisfies some technical structural conditions, then the following nice properties hold; these properties are mostly taken from (Lemma 5.2, Theorem 5.8, Davis et al. 2018) (where the structural condition is \(C^{1}\) Whitney stratifiability), which was slightly generalized in (Ji and Telgarsky 2020) under o-minimal definability; another alternative, followed in (Lyu and Li 2019), is to simply assume that a chain rule holds.

* **(Chain rule.)** For a.e. \(t\geq 0\) and every \(v\in\partial\widehat{\mathcal{R}}(w(t))\), then \(\frac{\mathrm{d}}{\mathrm{d}t}\widehat{\mathcal{R}}(w(t))=-\left\langle v, \dot{w}(t)\right\rangle\). This is the key strong property; since it holds for every element \(v\) of the Clarke differential simultaneously, it implies the next property.
* **(Minimum norm path.)** For almost every \(t\geq 0\), then \(\dot{w}(t)=-\arg\min\{\|v\|:v\in\partial\widehat{\mathcal{R}}(w(t))\}\). Consequently, $$\widehat{\mathcal{R}}(w(t))-\widehat{\mathcal{R}}(w(0))=\int_{0}^{t}\frac{ \mathrm{d}}{\mathrm{d}s}\widehat{\mathcal{R}}(w(s))\mathrm{d}s=-\int_{0}^{t} \min\{\|v\|^{2}:v\in\partial\widehat{\mathcal{R}}(w(s))\}\mathrm{d}s;$$ since the right hand size is nonpositive for all \(t\), the flow never increases the objective.

This allows us to reprove our stationary point guarantee from an earlier lecture: since

$$\widehat{\mathcal{R}}(w(t))-\widehat{\mathcal{R}}(w(0))=-\int_{0}^{t}\min\{\|v \|^{2}:v\in\partial\widehat{\mathcal{R}}(w(s))\}\mathrm{d}s\leq-t\min_{ \begin{subarray}{c}s\in[0,t]\\ v\in\partial\widehat{\mathcal{R}}(w(s))\end{subarray}}\|v\|^{2},$$

then just as before

$$\min_{\begin{subarray}{c}s\in[0,t]\\ v\in\partial\widehat{\mathcal{R}}(w(s))\end{subarray}}\|v\|^{2}\leq\frac{ \widehat{\mathcal{R}}(w(0))-\widehat{\mathcal{R}}(w(t))}{t},$$

thus for some time \(s\in[0,t]\), we have an iterate \(w(s)\) which is an approximate stationary point.

**Remark 9.1**: Let's go back to \(\dot{w}(t):=\arg\min\{\|v\|:v\in-\partial\widehat{\mathcal{R}}(w(t))\}\), which we said will hold almost everywhere.

This is _not_ satisfied by pytorch/tensorflow/jax/...

(Kakade and Lee 2018) gives some bad examples, e.g.,

$$x\mapsto\sigma(\sigma(x))-\sigma(-x)$$

with \(\sigma\) the ReLU, evaluated at \(0\). (Kakade and Lee 2018) also give a randomized algorithm for finding good subdifferentials.

Does it matter? In the NTK regime, few activations change. In practice, many change, but it's unclear what their effect is.

**9.1**: **Positive homogeneity**

Another tool we will use heavily outside convexity is _positive homogeneity_.

**Definition 9.2**: \(g\) is _positive homogeneous of degree \(L\)_ when \(g(\alpha x)=\alpha^{L}g(x)\) for \(\alpha\geq 0\). (We will only consider continuous \(g\), so \(\alpha>0\) suffices.)

**Example 9.1**:
* Single ReLU: \(\sigma(\alpha r)=\alpha\sigma(r)\).

* Monomials of degree \(L\) are positive homogeneous of degree \(L\): $$\prod_{i=1}^{d}(\alpha x_{i})^{p_{i}}=\alpha^{\sum_{i}p_{i}}\prod_{i}x_{i}^{p_{i} }=\alpha^{L}\prod_{i}x_{i}^{p_{i}}.$$

**Remark 9.2**: The math community also has a notion of homogeneity without positivity; the monomial example above works with \(\alpha<0\). Homogeneity in math is often tied to polynomials and generalizations thereof.

**Example 9.2**:
* A polynomial \(p(x)\) is \(L\)-homogeneous when all monomials have the same degree; by the earlier calculation, $$p(\alpha x)=\sum_{j=1}^{r}m_{j}(\alpha x)=\alpha^{L}\sum_{j=1}^{r}m_{j}(x).$$ The algebraic literature often discusses "homogeneous polynomials."
* Norms are 1-homogeneous, meaning \(\|\alpha x\|=\alpha\|x\|\) for \(\alpha>0\). But they moreover satisfy a stronger property \(\|\alpha x\|=|\alpha|\cdot\|x\|\) when \(\alpha<0\). Also, \(\ell_{p}\) norms are obtained by taking the root of a homogeneous polynomial, which in general changes the degree of a homogeneous function.
* Layers of a ReLU network are 1-homogeneous in the parameters for that layer: $$f(x;(W_{1},\ldots,\alpha W_{i},\ldots,W_{L}))$$ $$=W_{L}\sigma(W_{L-1}\sigma(\ldots\alpha W_{i}\sigma(\ldots W_{1}x \ldots)\ldots))$$ $$=\alpha W_{L}\sigma(W_{L-1}\sigma(\ldots W_{i}\sigma(\ldots W_{1}x \ldots)\ldots))$$ $$=\alpha f(x;w).$$ The _entire network_ is \(L\)-homogeneous in the full set of parameters: $$f(x;\alpha w) =f(x;(\alpha W_{1},\ldots,\alpha W_{L}))$$ $$=\alpha W_{L}\sigma(\alpha W_{L-1}\sigma(\ldots\sigma(\alpha W_{1 }x)\ldots))$$ $$=\alpha^{L}W_{L}\sigma(W_{L-1}\sigma(\ldots\sigma(W_{1}x)\ldots))$$ $$=\alpha^{L}f(x;w).$$ What is the homogeneity as a function of the input?
* Homework will cover some nonsmooth architectures that are _not_ positive homogeneous!

**9.2**: **Positive homogeneity and the Clarke differential**

Let's work out an element of the Clarke differential for a ReLU network

$$x\mapsto W_{L}\sigma_{L-1}(\cdots W_{2}\sigma_{1}(W_{1}x)).$$

As a function of \(x\), this mapping is 1-homogeneous and piecewise affine. As a function of \(w=(W_{L},\cdot,W_{1})\), it is \(L\)-homogeneous and piecewise polynomial. The boundary regions form a set of (Lebesgue) measure zero (wrt to either weights or parameters).

Fixing \(x\) and considering \(w\), interior to each piece, the mapping is differentiable. Due to the definition of Clarke differential, it therefore suffices to compute the gradients in all adjacent pieces, and then take their convex hull.

**Remark 9.3**: Note that we are _not_ forming the differential by choosing an arbitrary differential element for each ReLU: we are doing a more complicated region-based calculation. However, the former is what pytorch does.

So let's return to considering some \(w\) where are differentiable. Let \(A_{i}\) be a diagonal matrix with activations of the output after layer \(i\) on the diagonal:

$$A_{i}=\operatorname{diag}\left(\sigma^{\prime}(W_{i}\sigma(\ldots\sigma(W_{1}x) \ldots))\right),$$

(note we've baked in \(x\),) and so \(\sigma(r)=r\sigma^{\prime}(r)\) implies layer \(i\) outputs

$$x\mapsto A_{i}W_{i}\sigma(\ldots\sigma(W_{1}x)\ldots))=A_{i}W_{i}A_{i-1}W_{i-1 }\cdots A_{1}W_{1}x,$$

and the network outputs

$$f(x;w)=W_{L}A_{L-1}W_{L-1}A_{L-2}\cdots A_{1}W_{1}x.$$

and the gradient with respect to layer \(i\) is

$$\frac{\mathrm{d}}{\mathrm{d}W_{i}}f(x;w)=(W_{L}A_{L-1}\cdots W_{i+1}A_{i})^{ \mathsf{T}}(A_{i-1}W_{i-1}\cdots W_{1}x)^{\mathsf{T}}.$$

Additionally

$$\left\langle W_{i},\frac{\mathrm{d}}{\mathrm{d}W_{i}}f(x;w)\right\rangle =\left\langle W_{i},(W_{L}A_{L-1}\cdots W_{i+1}A_{i})^{\mathsf{T }}(A_{i-1}W_{i-1}\cdots W_{1}x)^{\mathsf{T}}\right\rangle$$ $$=\operatorname{tr}\left(W_{i}^{\mathsf{T}}(W_{L}A_{L-1}\cdots W_{ i+1}A_{i})^{\mathsf{T}}(A_{i-1}W_{i-1}\cdots W_{1}x)^{\mathsf{T}}\right)$$ $$=\operatorname{tr}\left((W_{L}A_{L-1}\cdots W_{i+1}A_{i})^{ \mathsf{T}}(W_{i}A_{i-1}W_{i-1}\cdots W_{1}x)^{\mathsf{T}}\right)$$ $$=\operatorname{tr}\left((W_{i}A_{i-1}W_{i-1}\cdots W_{1}x)^{ \mathsf{T}}(W_{L}A_{L-1}\cdots W_{i+1}A_{i})^{\mathsf{T}}\right)$$ $$=\operatorname{tr}\left(W_{L}A_{L-1}\cdots W_{i+1}A_{i}W_{i}A_{i -1}W_{i-1}\cdots W_{1}x\right)$$ $$=f(x;w),$$

and

$$\left\langle W_{i},\frac{\mathrm{d}}{\mathrm{d}W_{i}}f(x;w)\right\rangle=f(x;w )=\left\langle W_{i+1},\frac{\mathrm{d}}{\mathrm{d}W_{i+1}}f(x;w)\right\rangle.$$

This calculation can in fact be made much more general (indeed with a simpler proof!).

**Lemma 9.2**: Suppose \(f:\mathbb{R}^{d}\to\mathbb{R}\) is locally Lipschitz and \(L\)-positively homogeneous. For any \(w\in\mathbb{R}^{d}\) and \(s\in\partial f(w)\),

$$\left\langle s,w\right\rangle=Lf(w).$$

**Remark 9.4**: This statement appears in various places (Lyu and Li 2019); the version here is somewhat more general, and appears in (Ji and Telgarsky 2020).

**Proof.** If \(w=0\), then \(\left\langle s,w\right\rangle=0=Lf(w)\) for every \(s\in\partial f(w)\), so consider the case \(w\neq 0\). Let \(D\) denote those \(w\) where \(f\) is differentiable, and consider the case that \(w\in D\setminus\{0\}\). By the definition of gradient,

$$\lim_{\delta\downarrow 0}\frac{f(w+\delta w)-f(w)-\left\langle\nabla f(w), \delta w\right\rangle}{\delta\|w\|}=0,$$and by using homogeneity in the form \(f(w+\delta w)=(1+\delta)^{L}f(w)\) (for any \(\delta>0\)), then

$$0=\lim_{\delta\downarrow 0}\frac{\left((1+\delta)^{L}-1\right)f(w)-\langle\nabla f (w),\delta w\rangle}{\delta}=-\,\langle\nabla f(w),w\rangle+\lim_{\delta \downarrow 0}f(w)\left(L+\mathcal{O}(\delta)\right),$$

which implies \(\langle w,\nabla f(w)\rangle=Lf(w)\).

Now consider \(w\in\mathbb{R}^{d}\setminus D\setminus\{0\}\). For any sequence \((w_{i})_{i\geq 1}\) in \(D\) with \(\lim_{i}w_{i}=w\) for which there exists a limit \(s:=\lim_{i}\nabla f(w_{i})\), then

$$\langle w,s\rangle=\lim_{i\to\infty}\left\langle w_{i},\nabla f(w_{i})\right\rangle =\lim_{i\to\infty}Lf(w_{i})=Lf(w).$$

Lastly, for any element \(s\in\partial f(w)\) written in the form \(s=\sum_{i}\alpha_{i}s_{i}\) where \(\alpha_{i}\geq 0\) satisfy \(\sum_{i}\alpha_{i}=1\) and each \(s_{i}\) is a limit of a sequence of gradients as above, then

$$\langle w,s\rangle=\left\langle w,\sum_{i}\alpha_{i}s_{i}\right\rangle=\sum_{i }\alpha_{i}\left\langle w,s_{i}\right\rangle=\sum_{i}\alpha_{i}Lf(w)=Lf(w).$$

**Lemma 9.3**: **Norm preservation**__

If predictions are positive homogeneous with respect to each layer, then gradient flow preserves norms of layers.

**Lemma 9.3**: _(Simon S. Du, Hu, and Lee (2018))_ Suppose for \(\alpha>0\), \(f(x;(W_{L},\ldots,\alpha W_{i},\ldots,W_{1}))=\alpha f(x;w)\) (predictions are 1-homogeneous in each layer). Then for every pair of layers \((i,j)\), the gradient flow maintains

$$\frac{1}{2}\|W_{i}(t)\|^{2}-\frac{1}{2}\|W_{i}(0)\|^{2}=\frac{1}{2}\|W_{j}(t)\| ^{2}-\frac{1}{2}\|W_{j}(0)\|^{2}.$$

**Remark 9.5**: We'll assume a risk of the form \(\mathbb{E}_{k}\,\ell(y_{k}f(x_{k};w))\), but it holds more generally. We are also tacitly assuming we can invoke the chain rule, as discussed above.

**Proof.** Defining \(\ell^{\prime}_{k}(s):=y_{k}\ell^{\prime}(y_{k}f(x_{k};w(s)))\), and fixing a layer \(i\),

$$\frac{1}{2}\|W_{i}(t)\|^{2}-\frac{1}{2}\|W_{i}(0)\|^{2} =\int_{0}^{t}\frac{\mathrm{d}missing}{\mathrm{d}t}\frac{1}{2}\|W_ {i}(s)\|^{2}\mathrm{d}s$$ $$=\int_{0}^{t}\left\langle W_{i}(s),\dot{W}_{i}(s)\right\rangle \mathrm{d}s$$ $$=\int_{0}^{t}\left\langle W_{i}(s),-\mathop{\mathbb{E}}_{k}\ell^ {\prime}_{k}(s)\frac{\mathrm{d}f(x_{k};w)}{\mathrm{d}W_{i}(s)}\right\rangle \mathrm{d}s$$ $$=-\int_{0}^{t}\mathop{\mathbb{E}}_{k}\ell^{\prime}_{k}(s)f(x_{k} ;w)\mathrm{d}s.$$

This final expression does not depend on \(i\), which gives the desired equality.

**Remark 9.6**: One interesting application is to classification losses like \(\exp(-z)\) and \(\ln(1+\exp(-z))\), where \(\tilde{\mathcal{R}}(w)\to 0\) implies \(\min_{k}y_{k}f(x_{k};w)\to\infty\).

This by itself implies \(\|W_{j}\|\to\infty\) for _some_\(j\); combined with norm preservation, \(\min_{j}\|W_{j}\|\to\infty\)!

[ mjt(c): need to update this in light of the new material i've included?]

**9.4****Smoothness inequality adapted to ReLU**

Let's consider: single hidden ReLU layer, only bottom trainable:

$$f(x;w):=\frac{1}{\sqrt{m}}\sum_{j}a_{j}\sigma(\left\langle x,w_{j}\right\rangle ),\qquad a_{j}\in\{\pm 1\}.$$

Let \(W_{s}\in\mathbb{R}^{m\times d}\) denote parameters at time \(s\), suppose \(\|x\|\leq 1\).

$$\frac{\mathrm{d}f(x;W)}{\mathrm{d}W} =\begin{bmatrix}a_{1}x\sigma^{\prime}(w_{1}^{\mathsf{T}}x)/\sqrt{ m}\\ \vdots\\ a_{m}x\sigma^{\prime}(w_{m}^{\mathsf{T}}x)/\sqrt{m}\end{bmatrix},$$ $$\left\|\frac{\mathrm{d}f(x;W)}{\mathrm{d}W}\right\|_{\mathrm{F}}^ {2} =\sum_{j}\left\|a_{j}x\sigma^{\prime}(w_{j}^{\mathsf{T}}x)/\sqrt{ m}\right\|_{2}^{2}\leq\frac{1}{m}\sum_{j}\left\|x\right\|_{2}^{2}\leq 1.$$

We'll use the logistic loss, whereby

$$\ell(z) =\ln(1+\exp(-z)),$$ $$\ell^{\prime}(z) =\frac{-\exp(-z)}{1+\exp(-z)}\in(-1,0),$$ $$\widehat{\mathcal{R}}(W) :=\frac{1}{n}\sum_{k}\ell(y_{k}f(x_{k};W)).$$

A key fact (can be verified with derivatives) is

$$|\ell^{\prime}(z)|=-\ell^{\prime}(z)\leq\ell(z),$$

whereby

$$\frac{\mathrm{d}\widehat{\mathcal{R}}}{\mathrm{d}W} =\frac{1}{n}\sum_{k}\ell^{\prime}(y_{k}f(x_{k};W))y_{k}\nabla_{W} f(x_{k}W),$$ $$\left\|\frac{\mathrm{d}\widehat{\mathcal{R}}}{\mathrm{d}W}\right\| _{\mathrm{F}} \leq\frac{1}{n}\sum_{k}|\ell^{\prime}(y_{k}f(x_{k};W))|\cdot\|y_{ k}\nabla_{W}f(x_{k}W)\|_{\mathrm{F}}$$ $$\leq\frac{1}{n}\sum_{k}|\ell^{\prime}(y_{k}f(x_{k};W))|\leq\min \left\{1,\widehat{\mathcal{R}}(W)\right\}.$$

Now we can state a non-smooth, non-convex analog to +Theorem 7.3

**Lemma 9.4** (**(Lemma 2.6, Ji and Telgarsky 2019a)**): If \(\eta\leq 1\), for any \(Z\),

$$\|W_{t}-Z\|_{\mathrm{F}}^{2}+\eta\sum_{i<t}\widehat{\mathcal{R}}^{(i)}(W_{i}) \leq\|W_{0}-Z\|_{\mathrm{F}}^{2}+2\eta\sum_{i<t}\widehat{\mathcal{R}}^{(i)}(Z),$$

where \(\widehat{\mathcal{R}}^{(i)}(W)=\frac{1}{n}\sum_{k}\ell(y_{k}\left\langle W, \nabla f(x_{k};W_{i})\right\rangle)\).

**Remark 9.7**:

* \(\widehat{\mathcal{R}}^{(i)}(W_{i})=\widehat{\mathcal{R}}(W_{i})\).
* \(\widehat{\mathcal{R}}^{(i)}(Z)\approx\widehat{\mathcal{R}}(Z)\) if \(W_{i}\) and \(Z\) have similar activations.
* (Ji and Telgarsky 2019a) uses this in a proof scheme like (Chizat and Bach 2019): consider those iterations where the activations are similar, and then prove it actually happens a lot. (Ji and Telgarsky 2019a), with additional work, can use this to prove low _test_ error.

**Proof.** Using the squared distance potential as usual,

$$\|W_{i+1}-Z\|_{\mathrm{F}}^{2}=\|W_{i}-Z\|_{\mathrm{F}}^{2}-2\eta\left\langle \nabla\widehat{\mathcal{R}}(W_{i}),W_{i}-Z\right\rangle+\eta^{2}\|\nabla \widehat{\mathcal{R}}(W_{i})\|_{\mathrm{F}}^{2},$$

where \(\|\nabla\widehat{\mathcal{R}}(W_{i})\|_{\mathrm{F}}^{2}\leq\|\nabla\widehat{ \mathcal{R}}(W_{i})\|_{\mathrm{F}}\leq\widehat{\mathcal{R}}(W_{i})=\widehat{ \mathcal{R}}^{(i)}(W_{i})\), and

$$n\left\langle\nabla\widehat{\mathcal{R}}(W_{i}),Z-W_{i}\right\rangle$$ $$=\sum_{k}y_{k}\ell^{\prime}(y_{k}f(x_{k};W_{i}))\left\langle \nabla_{W}f(x_{k};W_{i}),Z-W_{i}\right\rangle$$ $$=\sum_{k}\ell^{\prime}(y_{k}f(x_{k};W_{i}))\left(y_{k}\left\langle \nabla_{W}f(x_{k};W_{i}),Z\right\rangle-y_{k}f(x_{k};W_{i})\right)$$ $$\leq\sum_{k}\left(\ell((y_{k}\left\langle\nabla_{W}f(x_{k};W_{i}), Z)\right\rangle-\ell(y_{k}f(x_{k};W_{i}))\right)$$ $$=n\left(\widehat{\mathcal{R}}^{(i)}(Z)-\widehat{\mathcal{R}}^{(i )}(W_{i})\right).$$

Together,

$$\|W_{i+1}-Z\|_{\mathrm{F}}^{2}\leq\|W_{i}-Z\|_{\mathrm{F}}^{2}+2\eta\left( \widehat{\mathcal{R}}^{(i)}(Z)-\widehat{\mathcal{R}}^{(i)}(W_{i})\right)+\eta \widehat{\mathcal{R}}_{i}(W_{i});$$

applying \(\sum_{i<t}\) to both sides gives the bound.

## 10 Margin maximization and implicit bias

During 2015-2016, various works pointed out that deep networks generalize well, even though parameter norms are large, and there is no explicit generalization (Neyshabur, Tomioka, and Srebro 2014; Zhang et al. 2017). This prompted authors to study _implicit bias of gradient descent_, the first such result being an analysis of linear predictors with _linearly separable data_, showing that gradient descent on the cross-entropy loss is implicitly biased towards a _maximum margin direction_ (Soudry, Hoffer, and Srebro 2017).

This in turn inspired many other works, handling other types of data, networks, and losses (Ji and Telgarsky 2019b, 2018, 2020; Gunasekar et al. 2018a; Lyu and Li 2019; Chizat and Bach 2020; Ji et al. 2020).

Margin maximization of first-order methods applied to exponentially-tailed losses was first proved for coordinate descent (Telgarsky 2013). The basic proof scheme there was pretty straightforward, and based on the similarity of the empirical risk (after the monotone transformation \(\ln(\cdot)\)) to \(\ln\sum\exp\), itself similar to \(\max(\cdot)\) and thus to margin maximization; we will use this connection as a basis for all proofs in this section (see also (Ji and Telgarsky 2019b; Gunasekar et al. 2018b)).

Throughout this section, fix training data \(((x_{i},y_{i}))_{i=1}^{n}\), define a (an unnormalized) _margin mapping_

$$m_{i}(w):=y_{i}f(x_{i};w);$$

by this choice, we can also conveniently write an **unnormalized risk**\(\mathcal{L}\):

$$\mathcal{L}(w):=\sum_{i}\ell(m_{i}(w))=\sum_{i}\ell(y_{i}f(x_{i};w)).$$

Throughout this section, we will always assume \(f\) is locally-Lipschitz and \(L\)-homogeneous in \(w\), which also means each \(m_{i}\) is locally-Lipschitz and \(L\)-homogeneous.

We will also use the exponential loss \(\ell(z)=\exp(-z)\). The results go through for similar losses.

**Remark 10.1** (generalization): As hinted before, margin maximization is one way gradient descent prefers a solution which has a hope to generalize well, and not merely achieve low empirical risk. This low generalization error of large-margin predictors will appear explicitly later on in section 13.4.

**Remark 10.2** (implicit bias): As mentioned above, the proofs here will show _implicit margin maximization_, which is enough to invoke the generalization theory in section 13.4. However, in certain cases it is valuable to moreover prove converges rates to the _maximum margin direction_. In the linear case, is is possible to convert a margin maximization rate to an implicit bias rate, however the rate degrades by a factor \(\sqrt{\cdot}\) (Ji and Telgarsky 2019b); analyzing the implicit bias without degradation in the rate is more involved, and not treated here (Soudry, Hoffer, and Srebro 2017).

**Remark 10.3** (squared loss): While the focus here is on losses with exponential tails and on bias towards the maximum margin direction, there are also many works (not further discussed here) which consider the squared loss (Gunasekar et al. 2017; Arora, Cohen, et al. 2018b, 2019).

**10.1** **Separability and margin maximization**

We just said "maximum margin" and "separable data." What do these mean?

Consider a linear predictor, meaning \(x\mapsto\left\langle w,x\right\rangle\) for some \(w\in\mathbb{R}^{d}\). This \(w\) "separates the data" if \(y_{i}\) and \(\operatorname{sgn}(\left\langle w,x_{i}\right\rangle)\) agree, which we can relax to the condition of _strict separability_, namely

$$\min_{i}y_{i}\left\langle w,x_{i}\right\rangle>0.$$

It seems reasonable, or a nice _inductive bias_, if we are as far from \(0\) as possible:

$$\max_{w\in?}\min_{i}y_{i}\left\langle w,x_{i}\right\rangle>0$$

The "?" indicates that we must somehow normalize or constrain, since otherwise, for separable data, this max becomes a sup and has value \(+\infty\).

**Definition 10.1**: Data is _linearly separable_ when there exists \(w\in\mathbb{R}^{d}\) so that \(\min_{i}y_{i}\left\langle w,x_{i}\right\rangle>0\). In this situation, the \((\ell_{2})\)_maximum margin predictor_ (which is unique!) is given by

$$\bar{u}:=\operatorname*{arg\,max}_{\left\|w\right\|=1}\min_{i}y_{i}\left\langle w,x_{i}\right\rangle,$$

and the margin is \(\gamma:=\min_{i}y_{i}\left\langle\bar{u},x_{i}\right\rangle\).

**Remark 10.4**: This concept has a long history. Margins first appeared in the classical perceptron analysis (Novikoff 1962), and maximum margin predictors were a guiding motivation for the SVM [mjt(r): need to add many more refs].

Consider now the general case of \(L\)-homogeneous predictors, where \(y_{i}\left\langle w,x_{i}\right\rangle\) is replaced by \(m_{i}(w)\).

**Proposition 10.1**: Suppose \(f(x;w)\) is \(L\)-homogeneous in \(w\), \(\ell\) is the exponential loss, and there exists \(\hat{w}\) with \(\widehat{\mathcal{R}}(\hat{w})<\ell(0)/n\). Then \(\inf_{w}\widehat{\mathcal{R}}(w)=0\), and the infimum is not attained.

**Proof.** Note

$$\max_{i}\ell(-m_{i}(\hat{w}))\leq\sum_{i}\ell(-m_{i}(\hat{w}))=n\widehat{ \mathcal{R}}(\hat{w})<\ell(0),$$

thus applying \(\ell^{-1}\) to both sides gives \(\min_{i}m_{i}(\hat{w}))>0\). Therefore

$$0\leq\inf_{w}\widehat{\mathcal{R}}(w)\leq\limsup_{c\to\infty}\widehat{ \mathcal{R}}(c\hat{w})=\sum_{i}\limsup_{c\to\infty}\ell(-m_{i}(c\hat{w}))=\sum _{i}\limsup_{c\to\infty}\ell(-c^{L}m_{i}(\hat{w}))=0.$$

This seems to be problematic; how can we "find" an "optimum," when solutions are off at infinity? Moreover, we do not even have unique directions, nor a way to tell different ones apart!

We can use margins, now appropriately generalized to the \(L\)-homogeneous case, to build towards a better-behaved objective function. First note that since

$$\min_{i}m_{i}(w)=\|w\|^{L}\min_{i}m_{i}\left(\frac{w}{\|w\|}\right),$$

we can compare different directions by normalizing the margin by \(\|w\|^{L}\). Moreover, again using the exponential loss,

$$\frac{\ell^{-1}\left(\mathcal{L}(w)\right)}{\|w\|^{L}}+\frac{\ln( n)}{\|w\|^{L}} =\frac{\ell^{-1}\left(\sum_{i}\ell(m_{i}(w))/n\right)}{\|w\|^{L}} \geq\frac{\min_{i}m_{i}(w)}{\|w\|^{L}}$$ $$=\frac{\ell^{-1}\left(\max_{i}\ell(m_{i}(w))\right)}{\|w\|^{L}} \tag{5}$$ $$\geq\frac{\ell^{-1}\left(\mathcal{L}(w)\right)}{\|w\|^{L}}.$$

This motivates the following definition.

**Definition 10.2**: Say the data is \(\vec{m}\)-separable when there exists \(w\) so that \(\min_{i}m_{i}(w)>0\). Define the margin, maximum margin, and smooth margin respectively as

$$\gamma(w):=\min_{i}m_{i}(w/\|w\|)=\frac{\min_{i}m_{i}(w)}{\|w\|^{L}},\qquad \bar{\gamma}:=\max_{\|w\|=1}\gamma(w),\qquad\bar{\gamma}(w):=\frac{\ell^{-1}( \mathcal{L}(w))}{\|w\|^{L}}. \tag{6}$$

**Remark 10.5**: decide something about \(w=0\ldots\).
**Remark 10.5**: The terminology "smoothed margin" is natural for \(L\)-homogeneous predictors, but even so it seems to have only appeared recently in (Lyu and Li 2019). In the 1-homogeneous case, the smoothed margin appeared much earlier, indeed throughout the boosting literature (Schapire and Freund 2012).
**Remark 10.6**: _(multiclass margins)_ There is also a natural notion of multiclass margin:

$$\min_{i}\frac{f(x_{i};w)_{y_{i}}-\max_{j\neq y_{i}}f(x_{i};w)_{j}}{\|w\|^{L}}.$$The natural loss to consider in this setting is the cross-entropy loss.

The basic properties can be summarized as follows.

**Proposition 10.2**: Suppose data is \(\vec{m}\)-separable. Then:

* \(\bar{\gamma}:=\max_{\|w\|\leq 1}\gamma(w)>0\) is well-defined (the maximum is attained).
* For any \(w\neq 0\), For any \(\hat{w}\) with \(\bar{\gamma}=\gamma(\hat{w})\), $$\lim_{c\to\infty}\bar{\gamma}(cw)=\gamma(w).$$ In particular, for \(\hat{w}\) satisfying \(\bar{\gamma}=\gamma(\hat{w})\), then \(\lim_{c\to\infty}\bar{\gamma}(c\hat{w})=\bar{\gamma}\).

**Proof.** The first part follows by continuity of \(m_{i}(w)\) and compactness of \(\{w\in\mathbb{R}^{p}:\|w\|=1\}\), and the second from eq. 6 and eq. 5.

**Remark 10.7**: For the linear case, margins have a nice geometric interpretation. This is not currently true for the general homogeneous case: there is no known reasonable geometric characterization of large margin predictors even for simple settings.

**10.2**: Gradient flow maximizes margins of linear predictors

Let's first see how far we can get in the linear case, using one of our earlier convex optimization tools, namely Theorem 7.4.

**Lemma 10.1**: Consider the linear case, with linearly separable data and the exponential loss, and \(\max_{i}\|x_{i}y_{i}\|\leq 1\). Then

$$\mathcal{L}(w_{t}) \leq\frac{1+\ln(2nt\gamma^{2})}{2t\gamma^{2}},$$ $$\|w_{t}\| \geq\ln(2tn\gamma^{2})-\ln\left(1+\ln(2tn\gamma^{2})\right).$$

**Remark 10.8**: The intuition we will follow for the proof is: _for every unit of norm, the (unnormalized) margin increases by at least \(\gamma\)_. Thus the margin bias affects the entire gradient descent process.

Later, when we study the \(L\)-homogeneous case, we are only able to show _for every unit norm (to the power \(L\)), the (unnormalized) margin increases by at least the current margin_, which implies nondecreasing, but not margin maximization.

**Proof.** By Theorem 7.4 with \(z=\ln(c)\bar{u}/\gamma\) for some \(c>0\),

$$\mathcal{L}(w(t)) \leq\mathcal{L}(z)+\frac{1}{2t}\left(\|z\|^{2}-\|w(t)-z\|^{2} \right)\leq\sum_{i}\ell(m_{i}(z))+\frac{\|z\|^{2}}{2t}$$ $$\leq\sum_{i}\exp(-\ln(c))+\frac{\ln(c)^{2}}{2t\gamma^{2}}=\frac{ n}{c}+\frac{\ln(c)^{2}}{2t\gamma^{2}},$$

and the first inequality follows from the choice \(c:=2tn\gamma^{2}\). For the lower bound on \(\|w_{t}\|\), usingthe preceding inequality,

$$\ell\left(\|w_{t}\|\right)\leq\min_{i}\ell(m_{i}(w_{t}))\leq\frac{1}{n}\mathcal{L} (w_{t})\leq\frac{1+\ln(2tn\gamma^{2})^{2}}{2tn\gamma^{2}},$$

and the second inequality follows by applying \(\ell^{-1}\) to both sides.

This nicely shows that we decrease the risk to \(0\), but not that we maximize margins. For this, we need a more specialized analysis.

**Theorem 10.1**: Consider the linear case, with linearly separable data and the exponential loss, and \(\max_{i}\|x_{i}y_{i}\|\leq 1\). Then

$$\gamma(w_{t})\geq\tilde{\gamma}(w_{t})\geq\bar{\gamma}-\frac{\ln n}{\ln t+\ln( 2n\gamma^{2})-2\ln\ln(2tne\gamma^{2})}$$

[ mjt(r): need to check some constants. also that denominator is hideous, maybe require slightly larger \(t\) to remove it?]

**Proof.** For convenience, define \(u(t):=\ell^{-1}(\mathcal{L}(w(t)))\) and \(v(t):=\|w(t)\|\), whereby

$$\gamma(w(t))=\frac{u(t)}{v(t)}=\frac{u(0)}{v(t)}+\frac{\int_{0}^{t}\dot{u}(s) \mathrm{d}s}{v(t)}.$$

Let's start by lower bounding the second term. Since \(\ell^{\prime}=-\ell\),

$$\dot{u}(t) =\left\langle\frac{-\nabla\mathcal{L}(w(t))}{\mathcal{L}(w(t))}, \dot{w}(t)\right\rangle=\frac{\|\dot{w}(t)\|^{2}}{\mathcal{L}(w(t))},$$ $$\|\dot{w}(s)\| \geq\left\langle\dot{w}(s),\bar{u}\right\rangle=\left\langle-\sum _{i}x_{i}y_{i}\ell^{\prime}(m_{i}(w(s))),\bar{u}\right\rangle$$ $$=\sum_{i}\ell(m_{i}(w(s)))\left\langle x_{i}y_{i},\bar{u}\right\rangle \geq\gamma\sum_{i}\ell(m_{i}(w(s)))=\gamma\mathcal{L}(w(s)),$$ $$v(t) =\|w(t)-w(0)\|=\left\|\int_{0}^{t}\dot{w}(s)\mathrm{d}s\right\| \leq\int_{0}^{t}\|\dot{w}(s)\|\,\mathrm{d}s,$$

thus

$$\frac{\int_{0}^{t}\dot{u}(s)\mathrm{d}s}{v(t)}\geq\frac{\int_{0}^{t}\frac{\| \dot{w}(s)\|^{2}}{\mathcal{L}(w(s))}\mathrm{d}s}{v(t)}=\frac{\int_{0}^{t}\| \dot{w}(s)\|\frac{\|\dot{w}(s)\|}{\mathcal{L}(w(s))}\mathrm{d}s}{v(t)}\geq \frac{\gamma\int_{0}^{t}\|\dot{w}(s)\|\mathrm{d}s}{v(t)}=\gamma.$$

For the first term \(u(0)/v(t)\), note \(\mathcal{L}(w(0))=n\) and thus \(u(0)=-\ln n\), whereas by the lower bound on \(\|w(t)\|\) from Lemma 10.1,

$$\frac{u(0)}{v(t)}=\frac{-\ln(n)}{\|w(t)\|}\geq\frac{-\ln(n)}{\ln(t)+\ln(2n \gamma^{2})-2\ln\ln(2tne\gamma^{2})}.$$

Combining these inequalities gives the bound.

We are maximizing margins, but at a glacial rate of \(1/\ln(t)\)!

To get some inspiration, notice that we keep running into \(\ell^{-1}(\mathcal{L}(w))\) in all the analysis. Why don't we just run gradient flow on this modified objective? In fact, the two gradient flows are the same!

**Remark 10.9**: _(time rescaling)_ Let \(w(t)\) be given by gradient flow on \(\mathcal{L}(w(t))\), and define a time rescaling \(h(t)\) via integration, namely so that \(\dot{h}(t)=1/\mathcal{L}(w(h(t)))\). Then, by the substitution rule for integration,

$$w(t)-w(0) =\int_{0}^{t}\dot{w}(s)\mathrm{d}s=-\int_{0}^{t}\nabla\mathcal{L}( w(s))\mathrm{d}s=\int_{h^{-1}([0,t])}\nabla\mathcal{L}(w(h(s))|\dot{h}(s)| \mathrm{d}s$$ $$=\int_{h^{-1}([0,t])}\frac{\nabla\mathcal{L}(w(h(s)))}{\mathcal{L }(w(h(s)))}\mathrm{d}s=\int_{h^{-1}([0,t])}\nabla\ln\mathcal{L}(w(h(s))\mathrm{ d}s$$

As such, the gradient flow on \(\mathcal{L}\) and on \(\ell^{-1}\circ\mathcal{L}\) are the same, modulo a _time rescaling_. This perspective was first explicitly stated by Chizat and Bach (2020), though _analyses_ using this rescaled time (and alternate flow characterization) existed before Lyu and Li (2019).

**Theorem 10.2**: _(time-rescaled flow)_ Consider linear predictors with linearly separable data, and the logistic loss. Suppose \(\dot{\theta}(t):=\nabla_{\theta}\ell^{-1}\mathcal{L}(\theta(t))\). Then

$$\gamma(\theta(t)\geq\tilde{\gamma}(\theta(t))\geq\gamma-\frac{\ln n}{t\gamma^{ 2}-\ln n}.$$

**Proof.** We start as before: set \(u(t):=\ell^{-1}\mathcal{L}(\theta(t))\) and \(v(t):=\|\theta(t)\|\); then

$$\tilde{\gamma}(t)=\frac{u(t)}{v(t)}=\frac{u(0)}{v(t)}+\frac{\int_{0}^{t}\dot{u} (s)\mathrm{d}s}{v(t)}=\frac{-\ln n}{v(t)}+\frac{\int_{0}^{t}\dot{u}(s)\mathrm{ d}s}{v(t)}.$$

Bounding these terms is now much simpler than for the regular gradient flow. Note

$$\|\dot{\theta}(s)\|\geq\left\langle\nabla\ln\mathcal{L}(\theta(s)),\bar{u} \right\rangle=\sum_{i}\frac{\ell^{\prime}(m_{i}(\theta(s)))}{\mathcal{L}( \theta(s))}\left\langle x_{i}y_{i},\bar{u}\right\rangle\geq\gamma\sum_{i}\frac{ \ell^{\prime}(m_{i}(\theta(s)))}{\mathcal{L}(\theta(s))}=\gamma,$$

$$\dot{u}(s)=\left\langle\nabla\ln\mathcal{L}(\theta(s)),\dot{\theta}(s)\right \rangle=\|\dot{\theta}(s)\|^{2},$$

thus

$$\ell^{-1}\mathcal{L}(\theta(t))=\ell^{-1}\mathcal{L}(\theta(0))+\int_{0}^{t} \frac{\mathrm{d}}{\mathrm{d}s}\ell^{-1}\mathcal{L}(\theta(s))\mathrm{d}s\geq- \ln(n)+t\gamma^{2},$$

$$\frac{\int_{0}^{t}\dot{u}(s)\mathrm{d}s}{v(t)}=\frac{\int_{0}^{t}\|\dot{\theta }(s)\|^{2}\mathrm{d}s}{v(t)}\geq\frac{\gamma\int_{0}^{t}\|\dot{\theta}(s)\| \mathrm{d}s}{v(t)}\geq\frac{\gamma\|\int_{0}^{t}\dot{\theta}(s)\mathrm{d}s\|} {v(t)}=\gamma.$$

On the other hand,

$$\|\theta(t)\|\gamma\geq\|\theta(t)\|\gamma(\theta(t))\geq\ell^{-1}\mathcal{L} (\theta(t))\geq t\gamma^{2}-\ln(n).$$

Together,

$$\gamma(t)=\frac{u(t)}{v(t)}\geq\gamma-\frac{\ln(n)}{t\gamma^{2}-\ln n}.$$

**Remark 10.10**: The preceding two proofs are simplified from (Ji and Telgarsky 2019b), but follow a general scheme from the (coordinate descent!) analysis in (Telgarsky 2013); this scheme was also followed in (Gunasekar et al. 2018b). The proof in (Soudry, Hoffer, and Srebro 2017) is different, and is based on an SVM analogy, since \(\tilde{\gamma}\to\gamma\).

Note also that the proofs here do not show \(w(t)\) converges to (the unique) maximum margin linear separator, which is easy to do with worse rates, and harder to do with good rates. However, large margins is sufficient for generalization in the linear case, as in section 13.4.

In the nonlinear case, we do not have a general result, and instead only prove that smoothed margins are nondecreasing.

**Theorem 10.3**: _(originally from (Lyu and Li 2019), simplification due to (Ji 2020))_

Consider the _Clarke flow_\(\dot{w}_{t}\in-\partial\ln\sum_{i}\exp(-m_{i}(w_{t}))\) with \(w_{0}=0\), and once again suppose the chain rule holds for almost all \(t\geq 0\). If there exists \(t_{0}\) with \(\tilde{\gamma}(w(t_{0}))>0\), then \(t\mapsto\tilde{\gamma}(w(t))\) is nondecreasingalong \([t_{0},\infty)\).

The proof will use the following interesting approximate homogeneity property of \(\ln\sum\exp\).

**Lemma 10.2**: _(taken from (Ji and Telgarsky 2020))_

For every \(w\) and every \(v\in-\partial\ln\sum\exp(-m_{i}(w))\), assuming the chain rule holds,

$$-L\ln\sum_{i}\exp(-m_{i}(w))\leq\left\langle v,w\right\rangle.$$

If \(-\ln\sum_{i}\exp\) were itself homogeneous, this would be an equality; instead, using only the \(L\)-homegeneity of \(m_{i}\), we get a lower bound.

**Proof.** Let \(v\in-\partial\ln\sum\exp(m_{i}(w))\) be given, whereby (thanks to assuming a chain rule) there exists \(v_{i}\in\partial m_{i}(w)\) for each \(i\) such that

$$v=\sum_{i=1}^{n}\frac{\exp(-m_{i}(w))v_{i}}{\sum_{j=1}^{m}\exp(-m_{j}(w))}.$$

Since \(\exp(-m_{k}(w))\geq 0\) for every \(k\) and since \(-\ln\) is monotone decreasing, Then

$$\left\langle v,w\right\rangle =\left\langle\sum_{i=1}^{n}\frac{\exp(-m_{i}(w))v_{i}}{\sum_{j=1} ^{m}\exp(-m_{j}(w))},w\right\rangle$$ $$=\sum_{i=1}^{n}\frac{\exp(-m_{i}(w))}{\sum_{j=1}^{m}\exp(-m_{j}(w ))}\left\langle v_{i},w\right\rangle$$ $$=L\sum_{i=1}^{n}\frac{\exp(-m_{i}(w))}{\sum_{j=1}^{m}\exp(-m_{j}( w))}m_{i}(w)$$ $$=L\sum_{i=1}^{n}\frac{\exp(-m_{i}(w))}{\sum_{j=1}^{m}\exp(-m_{j}( w))}\left(-\ln\exp(-m_{i}(w))\right)$$ $$\geq L\sum_{i=1}^{n}\frac{\exp(-m_{i}(w))}{\sum_{j=1}^{m}\exp(-m_ {j}(w))}\left(-\ln\sum_{k}\exp(-m_{k}(w))\right)$$ $$=-L\ln\sum_{k}\exp(-m_{k}(w))$$

as desired.

Lemma 10.2 (taken from (Ji and Telgarsky 2020)) leads to a fairly easy proof of Theorem 10.3 (originally from (Lyu and Li 2019), simplification due to (Ji 2020)).

**Proof of Theorem 10.3** (originally from (Lyu and Li 2019), simplification due to (Ji 2020)).: It will be shown that \((\mathrm{d}/\mathrm{d}t)\tilde{\gamma}(t)\geq 0\) whenever \(\tilde{\gamma}(t)>0\), which completes the proof via the following contradiction. Let \(t>t_{0}\) denote the earliest time where \(\tilde{\gamma}(t)<\tilde{\gamma}(t_{0})\). But that means \(\tilde{\gamma}(t^{\prime})>0\) for \(t^{\prime}\in[t_{0},t)\), whereby

$$\tilde{\gamma}(t)=\tilde{\gamma}(t_{0})+\int_{t_{0}}^{t}\frac{\mathrm{d}}{ \mathrm{d}s}\tilde{\gamma}(s)\mathrm{d}s\geq\tilde{\gamma}(t_{0})+0,$$

a contradiction, thus completing the proof.

To this end, fix any \(t\) with \(\tilde{\gamma}(t)>0\), and the goal is to show \((\mathrm{d}/\mathrm{d}t)\tilde{\gamma}(t)\geq 0\). Define

$$u(t):=-\ln\sum_{i}\exp(-m_{i}(w(t))),\qquad v(t):=\|w(t)\|^{L},$$

whereby \(\tilde{\gamma}(t):=\tilde{\gamma}(w(t)):=u(t)/v(t)\), and

$$\frac{\mathrm{d}}{\mathrm{d}t}\tilde{\gamma}(t)=\frac{\dot{u}(t)v(t)-u(t)\dot {v}(t)}{v(t)^{2}},$$

where \(v(t)>0\) since \(\tilde{\gamma}(t)>0\) is impossible otherwise, which means the ratio is well-defined. Making use of Lemma 10.2 (taken from (Ji and Telgarsky 2020)),

$$\dot{u}(t) =\|\dot{w}(t)\|^{2}$$ $$\geq\|\dot{w}(t)\|\left\langle\frac{w(t)}{\|w(t)\|},\dot{w}(t)\right\rangle$$ $$\geq\frac{Lu(t)\|\dot{w}(t)\|}{\|w(t)\|},$$ $$\dot{v}(t) =\frac{\mathrm{d}}{\mathrm{d}t}\|w(t)\|^{L/2}$$ $$=L\|w(t)\|^{L-1}\left\langle\frac{w(t)}{\|w(t)\|},\dot{w}(t)\right\rangle$$ $$\leq L\|w(t)\|^{L-1}\|\dot{w}(t)\|,$$

whereby

$$\dot{u}(t)v(t)-\dot{v}(t)u(t)\geq\frac{Lu(t)\|\dot{w}(t)\|}{\|w(t)\|}v(t)-u(t)L \|w(t)\|^{L-1}\|\dot{w}(t)\|=0,$$

which completes the proof.

**Remark 10.11**: The linear case achieves a better bound by having not only a unique global hard margin solution \(u\), but having the structural property \(\langle u,y_{i}x_{i}\rangle\geq\gamma\), which for instance implies \(\|\dot{w}(t)\|\geq\gamma\).

Instead, the preceding proof uses the much weaker inequality \(\|\dot{w}(t)\|\geq\frac{Lu(t)}{\|w(t)\|}\).
**Remark 10.12**: As mentioned, +Theorem 10.3 (originally from (Lyu and Li 2019), simplification due to (Ji 2020)) was originally presented in (Lyu and Li 2019), though this simplification is due to (Ji 2020), and its elements can be found throughout (Ji and Telgarsky 2020). The version in (Lyu and Li 2019) is significantly different, and makes heavy (and interesting) use of a _polar decomposition_ of homogeneous functions and gradient flow on them.

For the case of an infinite-width 2-homogeneous network, assuming a number of convergence properties of the flow (which look technical, but are not "merely technical," and indeed difficult to prove), margins are globally maximized (Chizat and Bach 2020).

Generalization: preface

The purpose of this generalization part is to bound the gap between testing and training error for standard (multilayer ReLU) deep networks via the classical uniform convergence tools, and also to present and develop these classical tools (based on Rademacher complexity).

These bounds are very loose, and there is extensive criticism now both of them and of the general approach, as will be discussed shortly (Neyshabur, Tomioka, and Srebro 2014; Zhang et al. 2017; Nagarajan and Kolter 2019; Dziugaite and Roy 2017); this work is ongoing and moving quickly and there are even already many responses to these criticisms (Negrea, Dziugaite, and Roy 2019; L. Zhou, Sutherland, and Srebro 2020; P. L. Bartlett and Long 2020).

**11.1** **Omitted topics**

* Domain adaptation / covariate shift.
* Generalization properties of more architectures. One key omission is of convolution layers; for one generalization analysis, see (Long and Sedghi 2019).
* Other approaches and perspectives on generalization (possibly changing the basic definitions of "generalization"), for instance:
* PAC-Bayes approaches (Dziugaite and Roy 2017). In the present notes, we only focus on _uniform convergence bounds_, which give high probability bounds between training and test error which hold simultaneously for every element of some class. By contrast, PAC-Bayes consider a _distribution_ over predictors, and bound the _expected_ gap between testing and training error for these predictors in terms of how close this distribution is to some prior distribution over the predictors.
* The looseness of the uniform-convergence bounds presented in these notes leads many authors to instead use them as _explanatory_ tools, e.g., by studying their _correlation_ with observed generalization. A correlation was claimed and presented in (P. Bartlett, Foster, and Telgarsky 2017), however it was on a single dataset and architecture. More extensive investigations have appeared recently (Jiang et al. 2020; Dziugaite et al. 2020), and highlight that while some bounds are correlated with generalization (or rather _predictive of generalization_) in some settings, there are other situations (e.g., large width) where no bound is correlated with observed generalization gaps.
* Compression-based approaches (Arora, Ge, et al. 2018), which bound the generalization of the network _after_ applying some compression procedure, with no guarantees on the original network; that said, it is a promising approach, and there has been some effort to recover guarantees on the original network (Suzuki, Abe, and Nishimura 2019). Another relevant work, from an explicitly PAC-Bayes perspective, is (W. Zhou et al. 2018). For further connections between PAC-Bayes methodology and compression, see (Blum and Langford 2003), and for more on the concept of compression _schemes_, see for instance (Moran and Yehudayoff 2015).
* Double descent (Belkin et al. 2018; Belkin, Hsu, and Xu 2019; Hastie et al. 2019), and related "interpolating predictors."
* Various omitted bounds in our uniform deviation framework:
* (Wei and Ma 2019) give a bound which requires smooth activations; if we convert it to ReLU, it introduces a large factor which does not seem to improve over those presented here. That said, it is an interesting bound and approach. (There are a number of other bounds we don't discuss since similarly they degrade for ReLU.)
* (Golowich, Rakhlin, and Shamir 2018) have an additional bound over the one of theirs we present here: interestingly, it weakens the depends on \(\sqrt{n}\) to \(n^{1/4}\) or \(n^{1/5}\) but in exchange vastly improves the dependence on norms in the numerator, and is a very interesting bound. **Concentration of measure**
* **Concentration of measure*
* studies how certain distribution families and operations on distributions lead to "clumping up" of probability mass. Examples we've seen:
* Gaussians concentrate around the one-standard-deviation shell; we used this in NTK to say few activations change (so it's concentrated _away_ from 0, sometimes this is called "anti-concentration").
* Azuma-Hoeffding gave us control on the errors in SGD; note that we averaged together many errors before studying concentration!
* We'll see in this section that concentration of measure allows us to handle the generalization gap of _single predictors fixed in advance_, but is insufficient to handle the output of training algorithms.
* We will be **absurdly brief.*
* Some other resources:
* Martin Wainwright's lecture notes (Wainwright 2015), now turned into a book (Wainwright 2019).
* My learning theory class, as well as Maxim Raginsky's. **sub-Gaussian random variables and Chernoff's bounding technique**

Our main concentration tool will be the _Chernoff bounding method_, which works nicely with _sub-Gaussian_ random variables.

**Definition 12.1**: Random variable \(Z\) is _sub-Gaussian with mean \(\mu\) and variance proxy \(\sigma^{2}\)_ when \(\mathbb{E}\,e^{\lambda(Z-\mu)}\leq e^{\lambda^{2}\sigma^{2}/2}\).

**Example 12.1**:
* Gaussian \(\mathcal{N}(\mu,\sigma^{2})\) is \((\mu,\sigma^{2})\)-sub-Gaussian.
* \(\sum_{i}Z_{i}\) is \((\sum_{i}\mu,\|\vec{\sigma}\|^{2})\) when \(Z_{i}\) is \((\mu_{i},\sigma^{2})\)-sub-Gaussian.
* If \(Z\in[a,b]\) a.s., then \(Z\) is \((\mathbb{E}\,Z,(b-a)^{2}/4)\)-sub-Gaussian (this is called the Hoeffding lemma [mjt(r): I should pick a proof.]).

**Remark 12.1**: There is also "sub-exponential"; we will not use it but it is fundamental.

Sometimes \(\mu\) is dropped from definition; in this case, one can study \(X-\mathbb{E}\,X\), and we'll just say "\(\sigma^{2}\)-sub-Gaussian."

\(\mathbb{E}\exp(\lambda Z)\) is the _moment generating function_ of \(Z\); it has many nice properties, though we'll only use it in a technical way.

sub-Gaussian random variables will be useful to us due to their vanishing tail probabilities. This indeed is an equivalent way to define sub-Gaussian (see (Wainwright 2015)), but we'll just prove implication.

**Theorem 12.1**: _(Markov's inequality)_ For any nonnegative r.v. \(X\) and \(\epsilon>0\),

$$\Pr[X\geq\epsilon]\leq\frac{\mathbb{E}\,X}{\epsilon}.$$

**Proof.** Apply \(\mathbb{E}\) to both sides of \(\epsilon\mathbf{1}[X\geq\epsilon]\leq X\).

**Corollary 12.1**: For any nonnegative, nondecreasing \(f\geq 0\) and \(f(\epsilon)>0\),

$$\Pr[X\geq\epsilon]\leq\frac{\mathbb{E}\,f(X)}{f(\epsilon)}.$$

**Proof.** Note \(\Pr[X\geq\epsilon]\leq\Pr[f(X)\geq f(\epsilon)]\) and apply Markov.

The Chernoff bounding technique is as follows. We can apply the proceeding corollary to the mapping \(t\mapsto\exp(tX)\) for all \(t>0\): supposing \(\mathbb{E}\,X=0\),

$$\Pr[X\geq\epsilon]=\inf_{t\geq 0}\Pr[\exp(tX)\geq\exp(t\epsilon)]\leq\inf_{t \geq 0}\frac{\mathbb{E}\exp(tX)}{\exp(t\epsilon)}.$$

Simplifying the RHS via sub-Guassianity,

$$\inf_{t>0}\frac{\mathbb{E}\exp(tX)}{\exp(t\epsilon)} \leq\inf_{t>0}\frac{\exp(t^{2}\sigma^{2}/2)}{\exp(t\epsilon)}= \inf_{t>0}\exp\left(t^{2}\sigma^{2}/2-t\epsilon\right)$$ $$=\exp\left(\inf_{t>0}t^{2}\sigma^{2}/2-t\epsilon\right).$$

The minimum of this convex quadratic is \(t:=\frac{\epsilon}{\sigma^{2}}>0\), thus

$$\Pr[X\geq\epsilon]=\inf_{t>0}\frac{\mathbb{E}\exp(tX)}{\exp(t\epsilon)}\leq \exp\left(\inf_{t>0}t^{2}\sigma^{2}/2-t\epsilon\right)=\exp\left(-\frac{ \epsilon^{2}}{2\sigma^{2}}\right). \tag{7}$$

What if we apply this to an average of sub-Gaussian r.v.'s? (The point is: this starts to look like an empirical risk!)

**Theorem 12.2**: _(Chernoff bound for subgaussian r.v.'s)_ Suppose \((X_{1},\ldots,X_{n})\) independent and respectively \(\sigma_{i}^{2}\)-subgaussian. Then

$$\Pr\left[\frac{1}{n}\sum_{i}X_{i}\geq\epsilon\right]\leq\exp\left(-\frac{n^{2 }\epsilon^{2}}{2\sum_{i}\sigma_{i}^{2}}\right).$$In other words ("inversion form"), with probability \(\geq 1-\delta\),

$$\frac{1}{n}\sum_{i}\mathbb{E}\,X_{i}\leq\frac{1}{n}\sum_{i}X_{i}+\sqrt{\frac{2 \sum_{i}\sigma_{i}^{2}}{n^{2}}\ln\left(\frac{1}{\delta}\right)}.$$

**Proof.**\(S_{n}:=\sum_{i}X_{i}/n\) is \(\sigma^{2}\)-subgaussian with \(\sigma^{2}=\sum_{i}\sigma_{i}^{2}/n^{2}\); plug this into the sub-Gaussian tail bound in eq. 7.

**Remark 12.2**: (Gaussian sanity check.) Let's go back to the case \(n=1\). It's possible to get a tighter tail for the Gaussian directly (see (Wainwright 2015)), but it only changes log factors in the "inversion form" of the bound. Note also the bound is neat for the Gaussian since it says the tail mass and density are of the same order (algebraically this makes sense, as with geometric series).

("Inversion" form.) This form is how things are commonly presented in machine learning; think of \(\delta\) as "confidence"; \(\ln(1/\delta)\) term means adding more digits to the confidence (e.g., bound holds with probability 99.999%) means a linear increase in the term \(\ln(1/\delta)\).

There are more sophisticated bounds (e.g., Bernstein, Freedman, McDiarmid) proved in similar ways, often considering a Martingale rather than IID r.v.s.

[ mjt(r): I should say something about necessary and sufficient, like convex lipschitz bounded vs lipschitz gaussian.]

[ mjt(r): maybe give heavy tail pointer? dunno.]

**12.2**: **Hoeffding's inequality and the need for uniform deviations**

Let's use what we've seen to bound misclassifications!

**Theorem 12.3**: _(Hoeffding inequality)_ Given independent \((X_{1},\ldots,X_{n})\) with \(X_{i}\in[a_{i},b_{i}]\) a.s.,

$$\Pr\left[\frac{1}{n}\sum_{i}(X_{i}-\mathbb{E}\,X_{i})\geq\epsilon\right]\leq \exp\left(-\frac{2n^{2}\epsilon^{2}}{\sum_{i}(b_{i}-a_{i})^{2}}\right).$$

**Proof.** Plug Hoeffding Lemma into sub-Gaussian Chernoff bound.

**Example 12.2**: Fix classifier \(f\), sample \(((X_{i},Y_{i}))_{i=1}^{n}\), and define \(Z_{i}:=\mathbf{1}[f(X_{i})\neq Y_{i}]\). With probability at least \(1-\delta\),

$$\Pr[f(X)\neq Y]-\frac{1}{n}\sum_{i=1}^{n}\mathbf{1}[f(x_{i})=y_{i}]=\mathbb{E }\,Z_{1}-\frac{1}{n}\sum_{i=1}^{n}Z_{i}\leq\sqrt{\frac{1}{2n}\ln\left(\frac{1 }{\delta}\right)}.$$

As in, test error is upper bounded by training error plus a term which goes \(\downarrow 0\) as \(n\to\infty\)!

**Example 12.3**: Classifier \(f_{n}\) memorizes training data:

$$f_{n}(x):=\begin{cases}y_{i}&x=x_{i}\in(x_{1},\ldots,x_{n}),\\ 17&\text{otherwise}.\end{cases}$$

Consider two situations with \(\Pr[Y=+1|X=x]=1\).

* Suppose marginal on \(X\) has finite support. Eventually (large \(n\)), this support is memorized and \(\widehat{\mathcal{R}}_{\mathsf{z}}(f_{n})=0=\mathcal{R}_{\mathsf{z}}(f_{n})\).
* Suppose marginal on \(X\) is continuous. With probability 1, \(\widehat{\mathcal{R}}_{\mathsf{z}}(f_{n})=0\) but \(\mathcal{R}_{\mathsf{z}}(f_{n})=1\)!

**What broke Hoeffding's inequality (and its proof) between these two examples?**

* \(f_{n}\) is a _random variable_ depending on \(S=((x_{i},y_{i}))_{i=1}^{n}\). Even if \(((x_{i},y_{i}))_{i=1}^{n}\) are independent, the new random variables \(Z_{i}:=\mathbf{1}[f_{n}(x_{i})\neq y_{i}]\) are not!

This \(f_{n}\)**overfit**: \(\widehat{\mathcal{R}}(f_{n})\) is small, but \(\mathcal{R}(f_{n})\) is large.

**Possible fixes.**

* **Two samples:** train on \(S_{1}\), evaluate on \(S_{2}\). But now we're using less data, and run into the same issue if we evaluate multiple predictors on \(S_{2}\).
* **Restrict access to data within training algorithm:** SGD does this, and has a specialized (martingale-based) deviation analysis.
* **Uniform deviations:** define a new r.v. controlling errors of _all possible predictors \(\mathcal{F}\) the algorithm might output_: $$\left[\sup_{f\in\mathcal{F}}\mathcal{R}(f)-\widehat{\mathcal{R}}(f)\right].$$ This last one is the approach we'll follow here. It can be adapted to data and algorithms by adapting \(\mathcal{F}\) (we'll discuss this more shortly).

**Remark 12.3**: There are measure-theoretic issues with the uniform deviation approach, which we'll omit here. Specifically, the most natural way to reason about

$$\left[\sup_{f\in\mathcal{F}}\mathcal{R}(f)-\widehat{\mathcal{R}}(f)\right]$$

is via uncountably intersections of events, which are not guaranteed to be within the \(\sigma\)-algebra. The easiest fix is to worth with countable subfamilies, which will work for the standard ReLU networks we consider.

## 13 Rademacher complexity

As before we will apply a brute-force approach to controlling generalization over a function family \(\mathcal{F}\): we will simultaneously control generalization for all elements of the class by working with the random variable

$$\left[\sup_{f\in\mathcal{F}}\mathcal{R}(f)-\widehat{\mathcal{R}}(f)\right].$$

This is called "uniform deviations" because we prove a deviation bound that holds _uniformly_ over all elements of \(\mathcal{F}\).

**Remark 13.1**: The idea is that even though our algorithms output predictors which depend on data, we circumvent the independence issue by invoking a uniform bound on all elements of \(\mathcal{F}\)_before_ we see the algorithm's output, and thus generalization is bounded for the algorithm output (and for everything else in the class). This is a brute-force approach because it potentially controls much more than is necessary.

On the other hand, we can adapt the approach to the output of the algorithm in various ways, as we will discuss after presenting the main Rademacher bound.

**Example 13.1** (_finite classes_): As an example of what is possible, suppose we have \(\mathcal{F}=(f_{1},\ldots,f_{k})\), meaning a finite function class \(\mathcal{F}\) with \(|\mathcal{F}|=k\). If we apply Hoeffding's inequality to each element of \(\mathcal{F}\) and then union bound, we get, with probability at least \(1-\delta\), for every \(f\in\mathcal{F}\),

$$\Pr[f(X)\neq Y]-\widehat{\Pr}[f(X)\neq Y]\leq\sqrt{\frac{\ln(k/\delta)}{2n}} \leq\sqrt{\frac{\ln|\mathcal{F}|}{2n}}+\sqrt{\frac{\ln(1/\delta)}{2n}}.$$

Rademacher complexity will give us a way to replace \(\ln|\mathcal{F}|\) in the preceding finite class example with something non-trivial in the case \(|\mathcal{F}|=\infty\).

**Definition 13.1** (_Rademacher complexity_): Given a set of vectors \(V\subseteq\mathbb{R}^{n}\), define the **(unnormalized) Rademacher complexity** as

$$\mathrm{URad}(V):=\mathbb{E}\sup_{u\in V}\left\langle\epsilon,u\right\rangle, \qquad\mathrm{Rad}(V):=\frac{1}{n}\mathrm{URad}(V),$$

where \(\mathbb{E}\) is uniform over the corners of the hypercube over \(\epsilon\in\{\pm 1\}^{n}\) (each coordinate \(\epsilon_{i}\) is a _Rademacher random variable_, meaning \(\Pr[\epsilon_{i}=+1]=\frac{1}{2}=\Pr[\epsilon_{i}=-1]\), and all coordinates are iid).

This definition can be applied to arbitrary elements of \(\mathbb{R}^{n}\), and is useful outside machine learning. We will typically apply it to the behavior of a function class on \(S=(z_{i})_{i=1}^{n}\):

$$\mathcal{F}_{|S}:=\{(f(x_{1}),\ldots,f(x_{n})):f\in\mathcal{F}\}\subseteq \mathbb{R}^{n}.$$

With this definition,

$$\mathrm{URad}(\mathcal{F}_{|S})=\mathbb{E}\sup_{\epsilon}\sup_{u\in\mathcal{F} _{|S}}\left\langle\epsilon,u\right\rangle=\mathbb{E}\sup_{\epsilon}\sup_{f\in \mathcal{F}}\sum_{i}\epsilon_{i}f(z_{i}).$$

**Remark 13.2** (Loss classes.): This looks like fitting random signs, but is not exactly that; often we apply it to the _loss class_: overloading notation,

$$\mathrm{URad}((\ell\circ\mathcal{F})_{|S})=\mathrm{URad}\left(\{(\ell(y_{1}f( x_{1})),\ldots,\ell(y_{n}f(x_{n}))):f\in\mathcal{F}\}\right).$$

**(Sanity checks.)** We'd like \(\mathrm{URad}(V)\) to measure how "big" or "complicated" \(V\) is. Here are a few basic checks:

1. \(\mathrm{URad}(\{u\})=\mathbb{E}\left\langle\epsilon,u\right\rangle=0\); this seems desirable, as a \(|V|=1\) is simple.
2. More generally, \(\mathrm{URad}(V+\{u\})=\mathrm{URad}(V)\).
3. If \(V\subseteq V^{\prime}\), then \(\mathrm{URad}(V)\leq\mathrm{URad}(V^{\prime})\).
4. \(\mathrm{URad}(\{\pm 1\}^{n})=\mathbb{E}_{\epsilon}\,\epsilon^{2}=n\); this also seems desirable, as \(V\) is as big/complicated as possible (amongst bounded vectors).
5. \(\mathrm{URad}(\{(-1,\ldots,-1),(+1,\ldots,+1)\})=\mathbb{E}_{\epsilon}\,|\sum_ {i}\epsilon_{i}|=\Theta(\sqrt{n})\). This also seems reasonable: \(|V|=2\) and it is not completely trivial.

**(URad vs Rad.)** I don't know other texts or even papers which use URad, I only see Rad. I prefer URad for these reasons:1. The \(1/n\) is a nuisance while proving Rademacher complexity bounds.
2. When we connect Rademacher complexity to covering numbers, we need to change the norms to account for this \(1/n\).
3. It looks more like a regret quantity.

**(Absolute value version.)** The original definition of Rademacher complexity (P. L. Bartlett and Mendelson 2002), which still appears in many papers and books, is

$$\text{URad}_{|\cdot|}(V)=\mathop{\mathbb{E}}_{\epsilon}\sup_{u\in V}\left| \left\langle\epsilon,u\right\rangle\right|.$$

Most texts now drop the absolute value. Here are my reasons:

1. \(\text{URad}_{|\cdot|}\) violates basic sanity checks: it is possible that \(\text{URad}_{|\cdot|}(\{u\})\neq 0\) and more generally \(\text{URad}_{|\cdot|}(V+\{u\})\neq\text{URad}_{|\cdot|}(V)\), which violates my basic intuition about a "complexity measure."
2. To obtain \(1/n\) rates rather than \(1/\sqrt{n}\), the notion of _local Rademacher complexity_ was introduced, which necessitated dropping the absolute value essentially due to the preceding sanity checks.
3. We can use \(\text{URad}\) to reason about \(\text{URad}_{|\cdot|}\), since \(\text{URad}_{|\cdot|}(V)=\text{URad}(V\cup-V)\).
4. While \(\text{URad}_{|\cdot|}\) is more convenient for certain operations, e.g., \(\text{URad}_{|\cdot|}(\cup_{i}V_{i})\leq\sum_{i}\text{URad}_{|\cdot|}(V_{i})\), there are reasonable surrogates for \(\text{URad}\) (as below).

The following theorem shows indeed that we can use Rademacher complexity to replace the \(\ln|\mathcal{F}|\) term from the finite-class bound with something more general (we'll treat the Rademacher complexity of finite classes shortly).

**Theorem 13.1** Let \(\mathcal{F}\) be given with \(f(z)\in[a,b]\) a.s. \(\forall f\in\mathcal{F}\).

1. With probability \(\geq 1-\delta\), $$\sup_{f\in\mathcal{F}}\mathop{\mathbb{E}}f(Z)-\frac{1}{n}\sum_{i}f(z_{i})\leq \mathop{\mathbb{E}}_{(z_{i})_{i=1}^{n}}\left(\sup_{f\in\mathcal{F}}\mathop{ \mathbb{E}}f(z)-\frac{1}{n}\sum_{i}f(z_{i})\right)+(b-a)\sqrt{\frac{\ln(1/ \delta)}{2n}}.$$
2. With probability \(\geq 1-\delta\), $$\mathop{\mathbb{E}}_{(z_{i})_{i=1}^{n}}\text{URad}(\mathcal{F}_{|S})\leq\text {URad}(\mathcal{F}_{|S})+(b-a)\sqrt{\frac{n\ln(1/\delta)}{2}}.$$
3. With probability \(\geq 1-\delta\), $$\sup_{f\in\mathcal{F}}\mathop{\mathbb{E}}f(Z)-\frac{1}{n}\sum_{i}f(z_{i})\leq \frac{2}{n}\text{URad}(\mathcal{F}_{|S})+3(b-a)\sqrt{\frac{\ln(2/\delta)}{2n}}.$$

**Remark 13.3** To flip which side has an expectation and which side has an average of random variables, replace \(\mathcal{F}\) with \(-\mathcal{F}:=\{-f:f\in\mathcal{F}\}\).

The proof of this bound has many interesting points and is spread out over the next few subsections. It has these basic steps:1. The _expected_ uniform deviations are upper bounded by the _expected_ Rademacher complexity. This itself is done in two steps: 1. The expected deviations are upper bounded by expected deviations between two finite samples. This is interesting since we could have reasonably defined generalization in terms of this latter quantity. 2. These two-sample deviations are upper bounded by expected Rademacher complexity by introducing random signs.
2. We replace this difference in expectations with high probability bounds via a more powerful concentration inequality which we haven't discussed, _McDiarmid's inequality_.

**Generalization** _without_ **concentration; symmetrization**

We'll use further notation throughout this proof.

$$\begin{array}{ll}Z&\mbox{r.v.; e.g., $(x,y)$,}\\ {\cal F}&\mbox{functions; e.g., $f(Z)=\ell(g(X),Y)$,}\\ \mathbb{E}&\mbox{expectation over $Z$,}\\ \mathbb{E}&\mbox{expectation over $(Z_{1},\ldots,Z_{n})$,}\\ \mathbb{E}\,f=\mathbb{E}\,f(Z),\\ \mathbb{E}_{n}f=\frac{1}{n}\sum_{i}f(Z_{i}).\end{array}$$

In this notation, \({\cal R}_{\ell}(g)=\mathbb{E}\,\ell\circ g\) and \(\widehat{\cal R}_{\ell}(g)=\widehat{\mathbb{E}}\ell\circ g\).

**Symmetrization with a ghost sample**

In this first step we'll introduce another sample ("ghost sample"). Let \((Z^{\prime}_{1},\ldots,Z^{\prime}_{n})\) be another iid draw from \(Z\); define \(\mathbb{E}^{\prime}_{n}\) and \(\widehat{\mathbb{E}}^{\prime}_{n}\) analogously.

**Symmetrization with a ghost sample**

In this first step we'll introduce another sample ("ghost sample"). Let \((Z^{\prime}_{1},\ldots,Z^{\prime}_{n})\) be another iid draw from \(Z\); define \(\mathbb{E}^{\prime}_{n}\) and \(\widehat{\mathbb{E}}^{\prime}_{n}\) analogously.

**Symmetrization with a ghost sample**

In this first step we'll introduce another sample ("ghost sample"). Let \((Z^{\prime}_{1},\ldots,Z^{\prime}_{n})\) be another iid draw from \(Z\); define \(\mathbb{E}^{\prime}_{n}\) and \(\widehat{\mathbb{E}}^{\prime}_{n}\) analogously.

**Symmetrization with a ghost sample**

In this first step we'll introduce another sample ("ghost sample"). Let \((Z^{\prime}_{1},\ldots,Z^{\prime}_{n})\) be another iid draw from \(Z\); define \(\mathbb{E}^{\prime}_{n}\) and \(\widehat{\mathbb{E}}^{\prime}_{n}\) analogously.

**Remark 13.4**: As above, in this section we are working only _in expectation_ for now. In the subsequent section, we'll get high probability bounds. But \(\sup_{f\in\mathcal{F}}\mathbb{E}\,f-\mathbb{E}_{n}^{\prime}f\) is a random variable; can describe it in many other ways too! (E.g., "asymptotic normality.")

As mentioned before, the preceding lemma says we can instead work with two samples. Working with two samples could have been our starting point (and definition of generalization): by itself it is a meaningful and interpretable quantity!

**13.1.2**: **Symmetrization with random signs**

The second step swaps points between the two samples; a magic trick with random signs boils this down into Rademacher complexity.

**Lemma 13.2**: \(\mathbb{E}_{n}\,\mathbb{E}_{n}^{\prime}\sup_{f\in\mathcal{F}}\left(\hat{ \mathbb{E}}_{n}^{\prime}f-\hat{\mathbb{E}}_{n}f\right)\leq\frac{2}{n}\, \mathbb{E}_{n}\,\mathrm{URad}(\mathcal{F}_{|S})\)_._

**Proof.** Fix a vector \(\epsilon\in\{-1,+1\}^{n}\) and define a r.v. \((U_{i},U_{i}^{\prime}):=(Z_{i},Z_{i}^{\prime})\) if \(\epsilon=1\) and \((U_{i},U_{i}^{\prime})=(Z_{i}^{\prime},Z_{i})\) if \(\epsilon=-1\). Then

$$\mathbb{E}_{n}^{\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\;\; \;

**Remark 13.5**: I'm omitting the proof. A standard way is via a _Martingale_ variant of the Chernoff bounding method. The Martingale adds one point at a time, and sees how things grow.

Hoeffding follows by setting \(F(\vec{Z})=\sum_{i}Z_{i}/n\) and verifying bounded differences \(c_{i}:=(b_{i}-a_{i})/n\).

**Proof of +Theorem 13.1.**

The third bullet item follows from the first two by union bounding. To prove the first two, it suffices to apply the earlier two lemmas on expectations and verify the quantities satisfy bounded differences with constant \((b-a)/n\) and \((b-a)\), respectively.

For the first quantity, for any \(i\) and \((z_{1},\ldots,z_{n},z^{\prime}_{i})\) and writing \(z^{\prime}_{j}:=z_{j}\) for \(z_{j}\neq z_{i}\) for convenience,

$$\left|\sup_{f\in\mathcal{F}}\mathbb{E}\,f-\widehat{\mathbb{E}}_{ n}f-\sup_{g\in\mathcal{F}}(\mathbb{E}\,g-\widehat{\mathbb{E}}^{\prime}_{n}g)\right| =\left|\sup_{f\in\mathcal{F}}\mathbb{E}\,f-\widehat{\mathbb{E}}_ {n}f-\sup_{g\in\mathcal{F}}(\mathbb{E}\,g-\widehat{\mathbb{E}}_{n}g+g(z_{i}) -g(z^{\prime}_{i}))\right|$$ $$\leq\sup_{h\in\mathcal{F}}\left|\sup_{f\in\mathcal{F}}\mathbb{E} \,f-\widehat{\mathbb{E}}_{n}f-\sup_{g\in\mathcal{F}}(\mathbb{E}\,g-\widehat{ \mathbb{E}}_{n}g+h(z_{i})/n-h(z^{\prime}_{i}))/n\right|$$ $$=\sup_{h\in\mathcal{F}}\left|h(z_{i})-h(z^{\prime}_{i}))\right|/n$$ $$\leq\frac{b-a}{n}.$$

Using similar notation, and additionally writing \(S\) and \(S^{\prime}\) for the two samples, for the Rademacher complexity,

$$\left|\mathrm{URad}(\mathcal{F}_{|S})-\mathrm{URad}(\mathcal{F}_ {|S^{\prime}})\right| =\left|\mathrm{URad}(\mathcal{F}_{|S})-\mathbb{E}\sup_{\epsilon} \sum_{f\in\mathcal{F}}\sum_{i=1}^{n}\epsilon_{i}f(z^{\prime}_{i})\right|$$ $$=\left|\mathrm{URad}(\mathcal{F}_{|S})-\mathbb{E}\sup_{\epsilon} \sum_{f\in\mathcal{F}}\sum_{i=1}^{n}\epsilon_{i}f(z_{i})-\epsilon_{i}f(z_{i}) +\epsilon_{i}f(z^{\prime}_{i})\right|$$ $$\leq\sup_{h\in\mathcal{F}}\left|\mathrm{URad}(\mathcal{F}_{|S})- \mathbb{E}\sup_{\epsilon}\sup_{f\in\mathcal{F}}\sum_{i=1}^{n}\epsilon_{i}f(z_ {i})-\epsilon_{i}h(z_{i})+\epsilon_{i}h(z^{\prime}_{i})\right|$$ $$\leq\sup_{h\in\mathcal{F}}\underset{\epsilon_{i}}{\mathbb{E}}| \epsilon_{i}h(z_{i})+\epsilon_{i}h(z^{\prime}_{i})|\leq(b-a).$$Let's consider logistic regression with bounded weights:

$$\ell(yf(x)) :=\ln(1+\exp(-yf(x))),$$ $$|\ell^{\prime}| \leq 1,$$ $$\mathcal{F} :=\left\{w\in\mathbb{R}^{d}:\|w\|\leq B\right\},$$ $$(\ell\circ\mathcal{F})_{|S} :=\left\{(\ell(y_{1}w^{\mathsf{T}}x_{1}),\ldots,\ell(y_{n}w^{ \mathsf{T}}x_{n})):\|w\|\leq B\right\},$$ $$\mathcal{R}_{\ell}(w) :=\mathbb{E}\,\ell(Yw^{\mathsf{T}}X),$$ $$\widehat{\mathcal{R}}_{\ell}(w) :=\frac{1}{n}\sum_{i}\ell(y_{i}w^{\mathsf{T}}x_{i}).$$

The goal is to control \(\mathcal{R}_{\ell}-\widehat{\mathcal{R}}_{\ell}\) over \(\mathcal{F}\) via the earlier theorem; our main effort is in controlling \(\text{URad}((\ell\circ\mathcal{F})_{S})\).

This has two steps:

* "Peeling" off \(\ell\).
* Rademacher complexity of linear predictors.

**Lemma 13.3**: Let \(\ell:\mathbb{R}^{n}\to\mathbb{R}^{n}\) be a vector of univariate \(L\)-lipschitz functions. Then \(\text{URad}(\ell\circ V)\leq L\cdot\text{URad}(V)\).

**Proof.** The idea of the proof is to "de-symmetrize" and get a difference of coordinates to which we can apply the definition of \(L\). To start,

$$\text{URad}(\ell\circ V) =\mathbb{E}\sup_{u\in V}\sum_{i}\epsilon_{i}\ell_{i}(u_{i})$$ $$=\frac{1}{2}\,\mathbb{E}\sup_{\epsilon_{2:n}}\sup_{u,w\in V} \left(\ell_{1}(u_{1})-\ell_{1}(w_{1})+\sum_{i=2}^{n}\epsilon_{i}(\ell_{i}(u_{i })+\ell_{i}(w_{i}))\right)$$ $$\leq\frac{1}{2}\,\mathbb{E}\sup_{\epsilon_{2:n}}\sup_{u,w\in V} \left(L|u_{1}-w_{1}|+\sum_{i=2}^{n}\epsilon_{i}(\ell_{i}(u_{i})+\ell_{i}(w_{i} ))\right).$$

To get rid of the absolute value, for any \(\epsilon\), by considering swapping \(u\) and \(w\),

$$\sup_{u,w\in V}\left(L|u_{1}-w_{1}|+\sum_{i=2}^{n}\epsilon_{i}( \ell_{i}(u_{i})+\ell_{i}(w_{i}))\right)$$ $$=\max\left\{\sup_{u,w\in V}\left(L(u_{1}-w_{1})+\sum_{i=2}^{n} \epsilon_{i}(\ell_{i}(u_{i})+\ell_{i}(w_{i}))\right),\right.$$ $$\qquad\left.\sup_{u,w}\left(L(w_{1}-u_{1})+\sum_{i=2}^{n}\epsilon _{i}(\ell_{i}(u_{i})+\ell_{i}(w_{i}))\right)\right\}$$ $$=\sup_{u,w\in V}\left(L(u_{1}-w_{1})+\sum_{i=2}^{n}\epsilon_{i}( \ell_{i}(u_{i})+\ell_{i}(w_{i}))\right).$$As such,

$$\text{URad}(\ell\circ V) \leq\frac{1}{2}\mathop{\mathbb{E}}_{\varepsilon_{2:n}}\sup_{u,w\in V }\left(L|u_{1}-w_{1}|+\sum_{i=2}^{n}\epsilon_{i}(\ell_{i}(u_{i})+\ell_{i}(w_{i}) )\right)$$ $$=\frac{1}{2}\mathop{\mathbb{E}}_{\varepsilon_{2:n}}\sup_{u,w\in V }\left(L(u_{1}-w_{1})+\sum_{i=2}^{n}\epsilon_{i}(\ell_{i}(u_{i})+\ell_{i}(w_{i} ))\right)$$ $$=\mathop{\mathbb{E}}_{\epsilon}\sup_{u\in V}\left[L\epsilon_{1}u_{ 1}+\sum_{i=2}^{n}\epsilon_{i}\ell_{i}(u_{i})\right].$$

Repeating this procedure for the other coordinates gives the bound.

Revisiting our overloaded composition notation:

$$\left(\ell\circ f\right) =\left((x,y)\mapsto\ell(-yf(x))\right),$$ $$\ell\circ\mathcal{F} =\left\{\ell\circ f:f\in\mathcal{F}\right\}.$$

**Corollary 13.1**: Suppose \(\ell\) is \(L\)-lipschitz and \(\ell\circ\mathcal{F}\in[a,b]\) a.s.. With probability \(\geq 1-\delta\), every \(f\in\mathcal{F}\) satisfies

$$\mathcal{R}_{\ell}(f)\leq\widehat{\mathcal{R}}_{\ell}(f)+\frac{2L}{n}\text{URad }(\mathcal{F}_{|S})+3(b-a)\sqrt{\frac{\ln(2/\delta)}{2n}}.$$

**Proof.** Use the lipschitz composition lemma with

$$|\ell(-y_{i}f(x_{i})-\ell(-y_{i}f^{\prime}(x_{i}))| \leq L|-y_{i}f(x_{i})+y_{i}f^{\prime}(x_{i}))|$$ $$\leq L|f(x_{i})-f^{\prime}(x_{i}))|.$$

Now let's handle step 2: Rademacher complexity of linear predictors (in \(\ell_{2}\)).

**Theorem 13.3**: Collect sample \(S:=(x_{1},\ldots,x_{n})\) into rows of \(X\in\mathbb{R}^{n\times d}\).

$$\text{URad}(\{x\mapsto\langle w,x\rangle:\|w\|_{2}\leq B\}_{|S}\})\leq B\|X\|_{ F}.$$

**Proof.** Fix any \(\epsilon\in\{-1,+1\}^{n}\). Then

$$\sup_{\|w\|\leq B}\sum_{i}\epsilon_{i}\left\langle w,x_{i}\right\rangle=\sup_ {\|w\|\leq B}\left\langle w,\sum_{i}\epsilon_{i}x_{i}\right\rangle=B\left\| \sum_{i}\epsilon_{i}x_{i}\right\|.$$

We'll bound this norm with Jensen's inequality (only inequality in whole proof!):

$$\mathop{\mathbb{E}}\left\|\sum_{i}\epsilon_{i}x_{i}\right\|=\mathop{\mathbb{ E}}\sqrt{\left\|\sum_{i}\epsilon_{i}x_{i}\right\|^{2}}\leq\sqrt{\mathop{ \mathbb{E}}\left\|\sum_{i}\epsilon_{i}x_{i}\right\|^{2}}.$$

To finish,

$$\mathop{\mathbb{E}}\left\|\sum_{i}\epsilon_{i}x_{i}\right\|^{2}=\mathop{ \mathbb{E}}\left(\sum_{i}\left\|\epsilon_{i}x_{i}\right\|^{2}+\sum_{i,j}\left \langle\epsilon_{i}x_{i},\epsilon_{j}x_{j}\right\rangle\right)=\mathop{ \mathbb{E}}\sum_{i}\left\|x_{i}\right\|^{2}=\|X\|_{F}^{2}.$$

**Remark 13.6**: By Khinchine's inequality, the preceding Rademacher complexity estimate is tight up to constants.

Let's now return to the logistic regression example!

**Example 13.2**_(logistic regression)_**: Suppose \(\|w\|\leq B\) and \(\|x_{i}\|\leq 1\), and the loss is the 1-Lipschitz logistic loss \(\ell_{\log}(z):=\ln(1+\exp(z))\). Note \(\ell(\langle w,yx\rangle)\geq 0\) and \(\ell(\langle w,yx\rangle)\leq\ln(2)+\langle w,yx\rangle\leq\ln(2)+B\).

Combining the main Rademacher bound with the Lipschitz composition lemma and the Rademacher bound on linear predictors, with probability at least \(1-\delta\), every \(w\in\mathbb{R}^{d}\) with \(\|w\|\leq B\) satisfies

$$\mathcal{R}_{\ell}(w) \leq\widehat{\mathcal{R}}_{\ell}(w)+\frac{2}{n}\mathrm{URad}(( \ell\circ\mathcal{F})_{|S})+3(\ln(2)+B)\sqrt{\ln(2/\delta)/(2n)}$$ $$\leq\widehat{\mathcal{R}}_{\ell}(w)+\frac{2B\|X\|_{F}}{n}+3(\ln( 2)+B)\sqrt{\ln(2/\delta)/(2n)}$$ $$\leq\widehat{\mathcal{R}}_{\ell}(w)+\frac{2B+3(B+\ln(2))\sqrt{\ln (2/\delta)/2}}{\sqrt{n}}.$$
**Remark 13.7**: (Average case vs worst case.) Here we replaced \(\|X\|_{F}\) with the looser \(\sqrt{n}\).

This bound scales as the SGD logistic regression bound proved via Azuma, despite following a somewhat different route (Azuma and McDiarmid are both proved with Chernoff bounding method; the former approach involves no symmetrization, whereas the latter holds for more than the output of an algorithm).

It would be nice to have an "average Lipschitz" bound rather than "worst-case Lipschitz"; e.g., when working with neural networks and the ReLU, which seems it can kill off many inputs! But it's not clear how to do this. Relatedly: regularizing the gradient is sometimes used in practice?

**13.4**: **Margin bounds**

In the logistic regression example, we peeled off the loss and bounded the Rademacher complexity of the predictors.

If most training labels are predicted not only accurately, but with a large margin, as in section 10, then we can further reduce the generalization bound.

Define \(\ell_{\gamma}(z):=\max\{0,\min\{1,1-z/\gamma\}\}\), \(\mathcal{R}_{\gamma}(f):=\mathcal{R}_{\ell_{\gamma}}(f)=\mathop{\mathbb{E}} \ell_{\gamma}(Yf(X))\), and recall \(\mathcal{R}_{\mathrm{z}}(f)=\Pr[f(X)\neq Y]\).

**Theorem 13.4**: For any margin \(\gamma>0\), with probability \(\geq 1-\delta\), \(\forall f\in\mathcal{F}\),

$$\mathcal{R}_{\mathrm{z}}(f)\leq\mathcal{R}_{\gamma}(f)\leq\widehat{\mathcal{R }}_{\gamma}(f)+\frac{2}{n\gamma}\mathrm{URad}(\mathcal{F})+3\sqrt{\frac{\ln(2 /\delta)}{2n}}.$$
**Proof.** Since

$$\mathbf{1}[\mathrm{sgn}(f(x))\neq y]\leq\mathbf{1}[-f(x)y\geq 0]\leq\ell_{ \gamma}(f(x)y),$$

then \(\mathcal{R}_{\mathrm{z}}(f)\leq\mathcal{R}_{\gamma}(f)\). The bound between \(\mathcal{R}_{\gamma}\) and \(\widehat{\mathcal{R}}_{\gamma}\) follows from the fundamental Rademacher bound, and by peeling the \(\frac{1}{\gamma}\)-Lipschitz function \(\ell_{\gamma}\).

[ mjt(): is that using per-example lipschitz? need to restate peeling? also, properly invoke peeling?]

**Remark 13.8**: _(bibliographic notes)_ As a generalization notion, this was first introduced for 2-layer networks in (P. L. Bartlett 1996), and then carried to many other settings (SVM, boosting,...) There are many different proof schemes; another one uses sparsification (Schapire et al. 1997). This approach is again being extensively used for deep networks, since it seems that while weight matrix norms grow indefinitely, the margins grow along with them (P. Bartlett, Foster, and Telgarsky 2017).

**13.5**: **Finite class bounds**

In our warm-up example of finite classes, our complexity term was \(\ln|\mathcal{F}|\). Here we will recover that, via Rademacher complexity. Moreover, the bound has a special form which will be useful in the later VC dimension and especially covering sections.

**Theorem 13.5**: _(Massart finite lemma)_ \(\operatorname{URad}(V)\leq\sup_{u\in V}\|u\|_{2}\sqrt{2\ln|V|}.\)

**Remark 13.9**: \(\ln|V|\) is what we expect from union bound. The \(\|\cdot\|_{2}\) geometry here is intrinsic here; I don't know how to replace it with other norms without introducing looseness. This matters later when we encounter the Dudley Entropy integral.

We'll prove this via a few lemmas.

**Lemma 13.4**: If \((X_{1},\ldots,X_{n})\) are \(c^{2}\)-subgaussian, then \(\operatorname{\mathbb{E}}\max_{i}X_{i}\leq c\sqrt{2\ln(n)}\).

**Proof.**

$$\operatorname{\mathbb{E}}\max_{i}X_{i} =\inf_{t>0}\operatorname{\mathbb{E}}\frac{1}{t}\ln\max_{i}\exp(tX _{i})\leq\inf_{t>0}\operatorname{\mathbb{E}}\frac{1}{t}\ln\sum_{i}\exp(tX_{i})$$ $$\leq\inf_{t>0}\frac{1}{t}\ln\sum_{i}\operatorname{\mathbb{E}}\exp (tX_{i})\leq\inf_{t>0}\frac{1}{t}\ln\sum_{i}\exp(t^{2}c^{2}/2)$$ $$=\inf_{t>0}(\ln(n)/t+c^{2}t/2)$$

and plug in minimizer \(t=\sqrt{2\ln(n)/c^{2}}\)

**Lemma 13.5**: If \((X_{1},\ldots,X_{n})\) are \(c_{i}^{2}\)-subgaussian and independent, \(\sum_{i}X_{i}\) is \(\|\vec{c}\|_{2}^{2}\)-subgaussian.

**Proof.** We did this in the concentration lecture, but here it is again:

$$\operatorname{\mathbb{E}}\exp(t\sum_{i}X_{i})=\prod_{i}\operatorname{\mathbb{ E}}\exp(tX_{i})\leq\prod_{i}\exp(t^{2}c_{i}^{2}/2)=\exp(t^{2}\|\vec{c}\|_{2}^{2} /2).$$

**Proof of +Theorem 13.5** (Massart finite lemma). Let \(\vec{\epsilon}\) be iid Rademacher and fix \(u\in V\). Define \(X_{u,i}:=\epsilon_{i}u_{i}\) and \(X_{u}:=\sum_{i}X_{u,i}\).

By Hoeffding lemma, \(X_{u,i}\) is \((u_{i}-u_{i})^{2}/4=u_{i}^{2}\) -subgaussian, thus (by Lemma) \(X_{u}\) is \(\|u\|_{2}^{2}\)-subgaussian. Thus

$$\operatorname{URad}(V)=\operatorname{\mathbb{E}}\max_{u\in V}\left\langle \epsilon,u\right\rangle=\operatorname{\mathbb{E}}\max_{u\in V}X_{u}\leq\max_{ u\in V}\|u\|_{2}\sqrt{2\ln|V|}.$$* The bounds we will prove shortly are all loose. To some extent, it was argued in (Neyshabur, Tomioka, and Srebro 2014; Zhang et al. 2017) and (Nagarajan and Kolter 2019) that this may be intrinsic to Rademacher complexity, though these arguments can be overturned in various settings (in the former, via _a posteriori_ bounds, e.g., as obtained via union bound; in the latter case, by considering a modified set of good predictors for the same problem); as such, that particular criticism is unclear. An alternative approach was highlighted in (Dziugaite and Roy 2017), however the bounds produced there are averages over some collection of predictors, and not directly comparable to the bounds here. Overall, though, many authors are investigating alternatives to the definition of generalization.
* Looking outside the specific setting of neural network generalization, Rademacher complexity has been widely adopted since, to a great extent, it can cleanly re-prove many existing bounds, and moreover elements of Rademacher complexity proofs exist many decades prior to the coining of the term (P. L. Bartlett and Mendelson 2002). However, already in these settings, Rademacher complexity has extensive weaknesses.
* For many learning problems, extensive effort was put into _fast_ or _optimal_ learning rates, which often boiled down to replacing a \(1/\sqrt{n}\) dependency with a \(1/n\). While _Local Rademacher Complexity_ is able to recover some of these bounds, it does not seem to recover all of them, and moreover the proofs are often very complicated.
* In many non-parametric learning settings, for example \(k\)-nearest-neighbor, the best bounds all use a direct analysis (Chaudhuri and Dasgupta 2014), and attempts to recover these analyses with Rademacher complexity have been unsuccessful.
* Closer to the investigation in these lecture notes, there are even cases where a direct Martingale analysis of SGD slightly beats the application of uniform convergence to the output of gradient descent, and similarly to the preceding case, attempts to close this gap have been unsuccessful (Ji and Telgarsky 2019a).

## 14 Two Rademacher complexity proofs for deep networks

We will give two bounds, obtained by inductively peeling off layers.

* One will depend on \(\|W_{i}^{\intercal}\|_{1,\infty}\). This bound has a pretty clean proof, and appeared in (P. L. Bartlett and Mendelson 2002).
* The other will depend on \(\|W_{i}^{\intercal}\|_{\text{F}}\), and is more recent (Golowich, Rakhlin, and Shamir 2018).

[ mjt(r): also i didn't mention yet that the other proof techniques reduce to this one?]

**14.1 First "layer peeling" proof: \((1,\infty)\) norm**

**Theorem 14.1**: Let \(\rho\)-Lipschitz activations \(\sigma_{i}\) satisfy \(\sigma_{i}(0)=0\), and

$$\mathcal{F}:=\{x\mapsto\sigma_{L}(W_{L}\sigma_{L_{1}}(\cdots\sigma_{1}(W_{1}x) \cdots)):\|W_{i}^{\intercal}\|_{1,\infty}\leq B\}$$Then \(\operatorname{URad}(\mathcal{F}_{|S})\leq\|X\|_{2,\infty}(2\rho B)^{L}\sqrt{2\ln(d)}\).

**Remark 14.1**: Notation \(\|M\|_{b,c}=\|(\|M_{:1}\|_{b},\ldots,\|M_{:d}\|_{b})\|_{c}\) means apply \(b\)-norm to columns, then \(c\)-norm to resulting vector.

Many newer bounds replace \(\|W_{i}^{\tau}\|\) with a distance to initialization. (The NTK is one regime where this helps.) I don't know how to use distance to initialize in the bounds in this section, but a later bound can handle it.

\((\rho B)^{L}\) is roughly a Lipschitz constant of the network according to \(\infty\)-norm bounded inputs. Ideally we'd have "average Lipschitz" not "worst case," but we're still far from that...

The factor \(2^{L}\) is not good and the next section gives one technique to remove it.

We'll prove this with an induction "peeling" off layers. This peeling will use the following lemma, which collects many standard Rademacher properties.

**Lemma 14.1**:
1. \(\operatorname{URad}(V)\geq 0\)_._
2. \(\operatorname{URad}(cV+\{u\})=|c|\operatorname{URad}(V)\)_._
3. \(\operatorname{URad}(\operatorname{conv}(V))=\operatorname{URad}(V)\)_._
4. _Let_ \((V_{i})_{i\geq 0}\) _be given with_ \(\sup_{u\in V_{i}}\left<u,\epsilon\right>\geq 0\)__\(\forall\epsilon\in\{-1,+1\}^{n}\)_. (E.g.,_ \(V_{i}=-V_{i}\)_, or_ \(0\in V_{i}\)_.) Then_ \(\operatorname{URad}(\cup_{i}V_{i})\leq\sum_{i}\operatorname{URad}(V_{i})\)_._
5. \(\operatorname{URad}(V)=\operatorname{URad}(-V)\)_._

**Remark 14.2**:
1. _is a mixed blessing: "Rademacher is insensitive to convex hulls,"_
2. _is true for_ \(\operatorname{URad}_{|\cdot|}\) _directly, where_ \(\operatorname{URad}_{|\cdot|}(V)=\mathbb{E}_{\epsilon}\sup_{u\in V}|\left< \epsilon,u\right>|\) _is the original definition of (unnormalized) Rademacher complexity: define_ \(W_{i}:=V_{i}\cup-V_{i}\)_, which satisfies the conditions, and note_ \((\cup_{i}V_{i})\cup-(\cup_{i}V_{i})=\cup_{i}W_{i}\)_. Since_ \(\operatorname{URad}_{|\cdot|}(V_{i})=\operatorname{URad}(W_{i})\)_, then_ \(\operatorname{URad}_{|\cdot|}(\cup_{i}V_{i})=\operatorname{URad}(\cup_{i}W_{i}) \leq\sum_{i\geq 1}\operatorname{URad}(W_{i})=\sum_{i\geq 1}\operatorname{URad}_{| \cdot|}(V_{i})\)_._ [_mjt(r)_: is this where i messed up and clipped an older Urada remark?]
3. _is important and we'll do the proof and some implications in homework._

**Proof of +Lemma 14.1**:
1. Fix any \(u_{0}\in V\); then \(\mathbb{E}_{\epsilon}\sup_{u\in V}\left<\epsilon,v\right>\geq\mathbb{E}_{ \epsilon}\left<\epsilon,u_{0}\right>=0\).
2. Can get inequality with \(|c|\)-Lipschitz functions \(\ell_{i}(r):=c\cdot r+u_{i}\); for equality, note \(-\epsilon c\) and \(\epsilon c\) are same in distribution.

3. This follows since optimization over a polytope is achieved at a corner. In detail, $$\mathrm{URad}(\mathrm{conv}(V)) =\mathop{\mathbb{E}}_{\epsilon}\sup_{\begin{subarray}{c}k\geq 1 \\ \alpha\in\Delta_{k}\end{subarray}}\sup_{u_{1},\ldots,u_{k}\in V}\left\langle \epsilon,\sum_{j}\alpha_{j}u_{j}\right\rangle$$ $$=\mathop{\mathbb{E}}_{\epsilon}\sup_{\begin{subarray}{c}k\geq 1\\ \alpha\in\Delta_{k}\end{subarray}}\sum_{j}\alpha_{j}\sup_{u_{j}\in V}\left\langle \epsilon,u_{j}\right\rangle$$ $$=\mathop{\mathbb{E}}_{\epsilon}\left(\sup_{\begin{subarray}{c}k \geq 1\\ \alpha\in\Delta_{k}\end{subarray}}\sum_{j}\alpha_{j}\right)\sup_{u\in V}\left\langle \epsilon,u\right\rangle$$ $$=\mathrm{URad}(V).$$
4. Using the condition, $$\mathop{\mathbb{E}}_{\epsilon}\sup_{u\in\cup_{i}V_{i}}\left\langle \epsilon,u\right\rangle =\mathop{\mathbb{E}}_{\epsilon}\sup_{i}\sup_{u\in V_{i}}\left\langle \epsilon,u\right\rangle\leq\mathop{\mathbb{E}}_{\epsilon}\sum_{i}\sup_{u\in V _{i}}\left\langle\epsilon,u\right\rangle$$ $$=\sum_{i\geq 1}\mathrm{URad}(V_{i}).$$
5. Since integrating over \(\epsilon\) is the same as integrating over \(-\epsilon\) (the two are equivalent distributions), $$\mathrm{URad}(-V)=\mathop{\mathbb{E}}_{\epsilon}\sup_{u\in V}\left\langle \epsilon,-u\right\rangle=\mathop{\mathbb{E}}_{\epsilon}\sup_{u\in V}\left\langle -\epsilon,-u\right\rangle=\mathrm{URad}(V).$$

**Proof of +Theorem 14.1.**

Let \(\mathcal{F}_{i}\) denote functions computed by nodes in layer \(i\). It'll be shown by induction that

$$\mathrm{URad}((\mathcal{F}_{i})_{|S})\leq\|X\|_{2,\infty}(2\rho B)^{i}\sqrt{2 \ln(d)}.$$

**Base case \((i=0)\)**: by the Massart finite lemma,

$$\mathrm{URad}((\mathcal{F}_{i})_{|S}) =\mathrm{URad}\left(\left\{x\mapsto x_{j}:j\in\left\{1,\ldots,d \right\}\right\}_{|S}\right)$$ $$\leq\left(\max_{j}\|(x_{1})_{j},\ldots,(x_{n})_{j}\|_{2}\right) \sqrt{2\ln(d)}$$ $$=\|X\|_{2,\infty}\sqrt{2\ln d}=\|X\|_{2,\infty}(2\rho B)^{0}\sqrt {2\ln d}.$$

**Inductive step.** Since \(0=\sigma(\left\langle 0,F(x)\right\rangle)\in\mathcal{F}_{i+1}\), applying both Lipschitz peeling and the preceding multi-part lemma,

$$\mathrm{URad}((\mathcal{F}_{i+1})_{|S})$$ $$=\mathrm{URad}\left(\left\{x\mapsto\sigma_{i+1}(\|W_{i+1}^{\tau} \|_{1,\infty}g(x)):g\in\mathrm{conv}(-\mathcal{F}_{i}\cup\mathcal{F}_{i}) \right\}_{|S}\right)$$ $$\leq\rho B\cdot\mathrm{URad}\left(-(\mathcal{F}_{i})_{|S}\cup( \mathcal{F}_{i})_{|S}\right)$$ $$\leq 2\rho B\cdot\mathrm{URad}\left((\mathcal{F}_{i})_{|S}\right)$$ $$\leq(2\rho B)^{i+1}\|X\|_{2,\infty}\sqrt{2\ln d}.$$

**Remark 14.3**: There are many related norm-based proofs now changing constants and also \((1,\infty)\); see for instance Neyshabur-Tomioka-Srebro, Bartlett-Foster-Telgarsky (we'll cover this), Golowich-Rakhlin-Shamir (we'll cover this), Barron-Klusowski.

The best lower bound is roughly what you get by writing a linear function as a deep network \(\hat{\cdot}_{\cdot}\).

The proof does not "coordinate" the behavior of adjacent layers in any way, and worst-cases what can happen.

_14.2_ **Second "layer peeling" proof: Frobenius norm**

**Theorem 14.2** ((Theorem 1, Golowich, Rakhlin, and Shamir 2018)): Let 1-Lipschitz positive homogeneous activation \(\sigma_{i}\) be given, and

$$\mathcal{F}:=\left\{x\mapsto\sigma_{L}(W_{L}\sigma_{L_{1}}(\cdots\sigma_{1}(W _{1}x)\cdots)):\|W_{i}\|_{\mathrm{F}}\leq B\right\}.$$

Then

$$\mathrm{URad}(\mathcal{F}_{|S})\leq B^{L}\|X\|_{\mathrm{F}}\left(1+\sqrt{2L\ln (2)}\right).$$

**Remark 14.4**: The criticisms of the previous layer peeling proof still apply, except we've removed \(2^{L}\).

The proof technique can also handle other matrix norms (though with some adjustment), bringing it closer to the previous layer peeling proof.

For an earlier version of this bound but including things like \(2^{L}\), see Neyshabur-Tomioka-Srebro. [ mjt(r): I need a proper citation]

The main proof trick (to remove \(2^{L}\)) is to replace \(\mathbb{E}_{\epsilon}\) with \(\ln\mathbb{E}_{\epsilon}\exp\); the \(2^{L}\) now appears inside the \(\ln\).

To make this work, we need two calculations, which we'll wrap up into lemmas.

* When we do "Lipschitz peeling," we now have to deal with \(\exp\) inside \(\mathbb{E}_{\epsilon}\). Magically, things still work, but the proof is nastier, and we'll not include it.
* That base case of the previous layer peeling could by handled by the Massart finite lemma; this time we end up with something of the form \(\mathbb{E}_{\epsilon}\exp(t\|X^{\top}\epsilon\|_{2})\).
* Comparing to the \(\infty\to\infty\) operator norm (aka \((1,\infty)\)) bound, let's suppose \(W\in\mathbb{R}^{m\times m}\) has row/node norm \(\|W_{j:}\|_{2}\approx 1\), thus \(\|W_{j:}\|_{1}\approx\sqrt{m}\), and $$\|W\|_{\mathrm{F}}\approx\sqrt{m}\approx\|W^{\top}\|_{1,\infty},$$ so this bound only really improves on the previous one by removing \(2^{L}\)?

Here is our refined Lipschitz peeling bound, stated without proof.

**Lemma 14.2** ((Eq. 4.20, Ledoux and Talagrand 1991)): Let \(\ell:\mathbb{R}^{n}\to\mathbb{R}^{n}\) be a vector of univariate \(\rho\)-lipschitz functions with \(\ell_{i}(0)=0\). Then

$$\mathbb{E}_{\epsilon}\exp\left(\sup_{u\in V}\sum_{i}\epsilon_{i}\ell_{i}(u_{i} )\right)\leq\mathbb{E}_{\epsilon}\exp\left(\rho\sup_{u\in V}\sum_{i}\epsilon_ {i}u_{i}\right).$$

**Remark 14.5**: With \(\exp\) gone, our proof was pretty clean, but all proofs I know of this are more complicated case analyses. So I will not include a proof \(\tilde{\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\, \,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\, \,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\, \,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\, \,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\, \,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\, \,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\, \,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\, \,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\, \,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\, \,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\, \,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\, \,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\, \,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\, \,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\, \,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\, \,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\, \,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\, \,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\, \,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\,\, \\(\mu:=\mathbb{E}\left\|X_{0}^{\intercal}\epsilon\right\|\) for convenience) and Jensen's inequality that

$$\text{URad}(\mathcal{F}_{|S}) =\mathbb{E}\sup_{w}\epsilon^{\intercal}X_{L}=\mathbb{E}\,\frac{1} {t}\ln\sup_{w}\exp\left(t\epsilon^{\intercal}X_{L}\right)$$ $$\leq\frac{1}{t}\ln\mathbb{E}\sup_{w}\exp\left(t|\epsilon^{ \intercal}X_{L}|\right)\leq\frac{1}{t}\ln\mathbb{E}\,2^{L}\exp\left(tB^{L}\| \epsilon^{\intercal}X_{0}\|\right)$$ $$\leq\frac{1}{t}\ln\mathbb{E}\,2^{L}\exp\left(tB^{L}(\|\epsilon^{ \intercal}X_{0}\|-\mu+\mu)\right)$$ $$\leq\frac{1}{t}\ln\left[2^{L}\exp\left(t^{2}B^{2L}\|X\|_{\text{F }}^{2}/2+tB^{L}\mu\right)\right]$$ $$\leq\frac{L\ln 2}{t}+\frac{tB^{2L}\|X\|_{\text{F}}^{2}}{2}+B^{L} \|X\|_{\text{F}},$$

whereby the final bound follows with the minimizing choice

$$t:=\sqrt{\frac{2L\ln(2)}{B^{2L}\|X\|_{\text{F}}^{2}}}\implies\text{URad}( \mathcal{F}_{|S})\leq\sqrt{2\ln(2)LB^{2L}\|X\|_{\text{F}}^{2}}+B^{L}\|X\|_{ \text{F}}.$$

The main inequality is now proved via induction.

For convenience, define \(\sigma:=\sigma_{i}\) and \(Y:=X_{i-1}\) and \(V:=W_{i}\) and \(\tilde{V}\) has \(\ell_{2}\)-normalized rows. By positive homogeneity and definition,

$$\sup_{w}\|\epsilon^{\intercal}X_{i}\|^{2} =\sup_{w}\sum_{j}(\epsilon^{\intercal}\sigma(YV^{\intercal}_{:j}) ^{2}$$ $$=\sup_{w}\sum_{j}(\epsilon^{\intercal}\sigma(YV^{\intercal}_{j:}) )^{2}$$ $$=\sup_{w}\sum_{j}(\epsilon^{\intercal}\sigma(\|V_{j:}\|Y\tilde{V }^{\intercal}_{j:}))^{2}$$ $$=\sup_{w}\sum_{j}\|V_{j:}\|^{2}(\epsilon^{\intercal}\sigma(Y \tilde{V}^{\intercal}_{j:}))^{2}.$$

The maximum over row norms is attained by placing all mass on a single row; thus, letting \(u\) denote an arbitrary unit norm (column) vector, and finally applying the peeling lemma, and re-introducing the dropped terms, and closing with the IH,

$$\mathbb{E}\exp\left(t\sqrt{\sup_{w}\|\epsilon^{\intercal}X_{i}\|^ {2}}\right) =\mathbb{E}\exp\left(t\sqrt{\sup_{w,u}B^{2}(\epsilon^{\intercal} \sigma(Yu))^{2}}\right)$$ $$=\mathbb{E}\sup_{\epsilon}\sup_{w,u}\exp\left(tB|\epsilon^{ \intercal}\sigma(Yu)|\right)$$ $$\leq\mathbb{E}\sup_{w,u}\exp\left(tB\epsilon^{\intercal}\sigma( Yu)\right)+\exp\left(-tB\epsilon^{\intercal}\sigma(Yu)\right)$$ $$\leq\mathbb{E}\sup_{\epsilon}\sup_{w,u}\exp\left(tB\epsilon^{ \intercal}\sigma(Yu)\right)+\mathbb{E}\sup_{\epsilon}\sup_{w,u}\exp\left(-tB \epsilon^{\intercal}\sigma(Yu)\right)$$ $$=\mathbb{E}\sup_{\epsilon}2\sup_{w,u}\exp\left(tB\epsilon^{ \intercal}\sigma(Yu)\right)$$ $$\leq\mathbb{E}\sup_{\epsilon}2\sup_{w,u}\exp\left(tB\epsilon^{ \intercal}Yu\right)$$ $$\leq\mathbb{E}\sup_{\epsilon}2\sup_{w}\exp\left(tB\|\epsilon^{ \intercal}Y\|_{2}\right)$$ $$\leq\mathbb{E}\sup_{\epsilon}2^{i}\sup_{w}\exp\left(tB^{i}\| \epsilon^{\intercal}X_{0}\|_{2}\right).$$

**Definition 15.1**: Given a set \(U\), scale \(\epsilon\), norm \(\|\cdot\|\), \(V\subseteq U\) is a **(proper) cover** when

$$\sup_{a\in U}\inf_{b\in V}\|a-b\|\leq\epsilon.$$

Let \(\mathcal{N}(U,\epsilon,\|\cdot\|)\) denote the **covering number**: the minimum cardinality (proper) cover.

**Remark 15.1**: "Improper" covers drop the requirement \(V\subseteq U\). (We'll come back to this.)

Most treatments define special norms with normalization \(1/n\) baked in; we'll use unnormalized Rademacher complexity and covering numbers.

Although the definition can handle directly covering functions \(\mathcal{F}\), we get nice bounds by covering \(\mathcal{F}_{|S}\), and conceptually it also becomes easier, just a vector (or matrix) covering problem with vector (and matrix) norms.

**Definition 15.1**: Given \(U\subseteq\mathbb{R}^{n}\),

$$\text{URad}(U)\leq\inf_{\alpha>0}\left(\alpha\sqrt{n}+\left(\sup_{a\in U}\|a \|_{2}\right)\sqrt{2\ln\mathcal{N}(U,\alpha,\|\cdot\|_{2})}\right).$$

**Remark 15.2**: \(\|\cdot\|_{2}\) comes from applying Massart. It's unclear how to handle other norms without some technical slop.
**Proof.** Let \(\alpha>0\) be arbitrary, and suppose \(\mathcal{N}(U,\alpha,\|\cdot\|_{2})<\infty\) (otherwise bound holds trivially).

Let \(V\) denote a minimal cover, and \(V(a)\) its closest element to \(a\in U\). Then

$$\operatorname{URad}(U) =\mathbb{E}\sup_{a\in U}\langle\epsilon,a\rangle$$ $$=\mathbb{E}\sup_{a\in U}\langle\epsilon,a-V(a)+V(a)\rangle$$ $$=\mathbb{E}\sup_{a\in U}\left(\langle\epsilon,V(a)\rangle+\langle \epsilon,a-V(a)\rangle\right)$$ $$\leq\mathbb{E}\sup_{a\in U}\left(\langle\epsilon,V(a)\rangle+\| \epsilon\|\cdot\|a-V(a)\|\right)$$ $$\leq\operatorname{URad}(V)+\alpha\sqrt{n}$$ $$\leq\sup_{b\in V}(\|b\|_{2})\sqrt{2\ln|V|}+\alpha\sqrt{n}$$ $$\leq\sup_{a\in U}(\|a\|_{2})\sqrt{2\ln|V|}+\alpha\sqrt{n},$$

and the bound follows since \(\alpha>0\) was arbitrary.

**Remark 15.3**: The same proof handles improper covers with minor adjustment: for every \(b\in V\), there must be \(U(b)\in U\) with \(\|b-U(v)\|\leq\alpha\) (otherwise, \(b\) can be moved closer to \(U\)), thus

$$\sup_{b\in V}\|b\|_{2}\leq\sup_{b\in V}\|b-U(b)\|_{2}+\|U(b)\|_{2}\leq\alpha+ \sup_{a\in U}\|a\|_{2}.$$

To handle other norms, superficially we need two adjustments: Cauchy-Schwarz can be replaced with Holder, but it's unclear how to replace Massart without slop relating different norms.

**Theorem 15.2**: **Second Rademacher-covering relationship: Dudley's entropy integral**

There is a classical proof that says that covering numbers and Rademacher complexities are roughly the same; the upper bound uses the Dudley entropy integral, and the lower bound uses a "Sudakov lower bound" which we will not include here.

[ mjt(c): crappy commitment, needs to be improved.]

* The Dudley entropy integral works at _multiple scales_.
* Suppose we have covers \((V_{N},V_{N-1},...)\) at scales \((\alpha_{N},\alpha_{N}/2,\alpha_{N}/4,\ldots)\).
* Given \(a\in U\), choosing \(V_{i}(a):=\arg\min_{b\in V_{i}}\|a-b\|\), $$a=(a-V_{N}(a))+(V_{N}(a)-V_{N-1}(a))+(V_{N-1}(a)-V_{N-2}(a))+\cdots.$$ We are thus rewriting \(a\) as a sequence of **increments*
* at different scales.
* One way to think of it is as writing a number as its binary expansion $$x=(0.b_{1}b_{2}b_{3}\ldots)=\sum_{i\geq 1}\frac{(b_{i}.b_{i+1}\ldots)-(0.b_{i+1} \ldots)}{2^{i}}=\sum_{i\geq 1}\frac{b_{i}}{2^{i}}.$$ In the Dudley entropy integral, we are covering these **increments**\(b_{i}\), rather than the number \(x\) directly.

**One can cover increments via covering numbers for the base set, and that is why these basic covering numbers appear in the Dudley entropy integral. But internally, the argument really is about these increments.**

**[ mjt(r): Seems this works with improper covers. I should check carefully and include it in the statement or a remark.]**

**[ mjt(r): citation for dudley? to dudley lo!?]**

**Theorem 15.2**: _(Dudley) Let \(U\subseteq[-1,+1]^{n}\) be given with \(0\in U\)._

$$\operatorname{URad}(U) \leq\inf_{N\in\mathbb{Z}_{\geq 1}}\left(n\cdot 2^{-N+1}+6\sqrt{n} \sum_{i=1}^{N-1}2^{-i}\sqrt{\ln\mathcal{N}(U,2^{-i}\sqrt{n},\|\cdot\|_{2}}\right)$$ $$\leq\inf_{\alpha>0}\left(4\alpha\sqrt{n}+12\int_{\alpha}^{\sqrt{n }/2}\sqrt{\ln\mathcal{N}(U,\beta,\|\cdot\|_{2}}\mathrm{d}\beta\right).$$

**Proof.** We'll do the discrete sum first. The integral follows by relating an integral to its Riemann sum.

* Let \(N\geq 1\) be arbitrary.
* For \(i\in\{1,\ldots,N\}\), define scales \(\alpha_{i}:=\sqrt{n}2^{1-i}\).
* Define cover \(V_{1}:=\{0\}\); since \(U\subseteq[-1,+1]^{n}\), this is a minimal cover at scale \(\sqrt{n}=\alpha_{1}\).
* Let \(V_{i}\) for \(i\in\{2,\ldots,N\}\) denote any minimal cover at scale \(\alpha_{i}\), meaning \(|V_{i}|=\mathcal{N}(U,\alpha_{i},\|\cdot\|_{2})\).

Since \(U\ni a=(a-V_{N}(a))+\sum_{i=1}^{N-1}\left(V_{i+1}(a)-V_{i}(a)\right)+V_{1}(a)\),

$$\operatorname{URad}(U)$$ $$=\mathbb{E}\sup_{a\in U}\left\langle\epsilon,a\right\rangle$$ $$=\mathbb{E}\sup_{a\in U}\left(\left\langle\epsilon,a-V_{N}(a) \right\rangle+\sum_{i=1}^{N-1}\left\langle\epsilon,V_{i+1}(a)-V_{i}(a)\right \rangle+\left\langle\epsilon,V_{1}(a)\right\rangle\right)$$ $$\leq\mathbb{E}\sup_{a\in U}\left\langle\epsilon,a-V_{N}(a)\right\rangle$$ $$\qquad+\sum_{i=1}^{N-1}\mathbb{E}\sup_{a\in U}\left\langle \epsilon,V_{i+1}-V_{i}(a)\right\rangle$$ $$\qquad+\mathbb{E}\sup_{a\in U}\left\langle\epsilon,V_{1}(a) \right\rangle.$$

Let's now control these terms separately.

The first and last terms are easy:

$$\mathbb{E}\sup_{a\in U}\epsilon V_{1}(a) =\mathbb{E}\left\langle\epsilon,0\right\rangle=0,$$ $$\mathbb{E}\sup_{a\in U}\left\langle\epsilon,a-V_{N}(a)\right\rangle \leq\mathbb{E}\sup_{a\in U}\|\epsilon\|\|a-V_{N}(a)\|\leq\sqrt{n} \alpha_{N}=n2^{1-N}.$$

For the middle term, define **increment class**\(W_{i}:=\{V_{i+1}(a)-V_{i}(a):a\in U\}\), whereby\(|W_{i}|\leq|V_{i+1}|\cdot|V_{i}|\leq|V_{i+1}|^{2}\), and

$$\mathbb{E}\sup_{a\in U}\left\langle\epsilon,V_{i+1}(a)-V_{i}(a) \right\rangle=\text{URad}(W_{i})$$ $$\leq\left(\sup_{w\in W_{i}}\|w\|_{2}\right)\sqrt{2\ln|W_{i}|}\leq \left(\sup_{w\in W_{i}}\|w\|_{2}\right)\sqrt{4\ln|V_{i+1}|},$$ $$\sup_{w\in W_{i}}\|w\|\leq\sup_{a\in U}\|V_{i+1}\|+\|a-V_{i}(a)\| \leq\alpha_{i+1}+\alpha_{i}=3\alpha_{i+1}.$$

Combining these bounds,

$$\text{URad}(U)\leq n2^{1-N}+0+\sum_{i=1}^{N}6\sqrt{n}2^{-i}\sqrt{\ln\mathcal{N }(U,2^{-i}\sqrt{n},\|\cdot\|_{2}}.$$

\(N\geq 1\) was arbitrary, so applying \(\inf_{N\geq 1}\) gives the first bound.

Since \(\ln\mathcal{N}(U,\beta,\|\cdot\|_{2})\) is nonincreasing in \(\beta\), the integral upper bounds the Riemann sum:

$$\text{URad}(U) \leq n2^{1-N}+6\sum_{i=1}^{N-1}\alpha_{i+1}\sqrt{\ln\mathcal{N}(U,\alpha_{i+1},\|\cdot\|)}$$ $$=n2^{1-N}+12\sum_{i=1}^{N-1}\left(\alpha_{i+1}-\alpha_{i+2}\right) \sqrt{\ln\mathcal{N}(U,\alpha_{i+1},\|\cdot\|)}$$ $$\leq\sqrt{n}\alpha_{N}+12\int_{\alpha_{N+1}}^{\alpha_{2}}\sqrt{\ln \mathcal{N}(U,\alpha_{i+1},\|\cdot\|)}\text{d}\beta.$$

To finish, pick \(\alpha>0\) and \(N\) with

$$\alpha_{N+1}\geq\alpha>\alpha_{N+2}=\frac{\alpha_{N+1}}{2}=\frac{\alpha_{N+2}} {4},$$

whereby

$$\text{URad}(U) \leq\sqrt{n}\alpha_{N}+12\int_{\alpha_{N+1}}^{\alpha_{2}}\sqrt{ \ln\mathcal{N}(U,\alpha_{i+1},\|\cdot\|)}\text{d}\beta$$ $$\leq 4\sqrt{n}\alpha+12\int_{\alpha}^{\sqrt{n}/2}\sqrt{\ln\mathcal{ N}(U,\alpha_{i+1},\|\cdot\|)}\text{d}\beta.$$

**Remark 15.4**: Tightness of Dudley: Sudakov's lower bound says there exists a universal \(C\) with

$$\text{URad}(U)\geq\frac{c}{\ln(n)}\sup_{\alpha>0}\alpha\sqrt{\ln\mathcal{N}(U, \alpha,\|\cdot\|)},$$

which implies \(\text{URad}(U)=\widetilde{\Theta}\left(\text{Dudley entropy integral}\right)\). [ mjt(c): needs references, detail, explanation.]

Taking the notion of increments to heart and generalizing the proof gives the concept of **chaining**. One key question there is tightening the relationship with Rademacher complexity (shrinking constants and log factors in the above bound).

Another term for covering is "metric entropy."

Recall once again that we drop the normalization \(1/n\) from URad and the choice of norm when covering.

Two deep network covering number bounds

We will give two generalization bounds.

* The first will be for arbitrary Lipschitz functions, and will be horifically loose (exponential in dimension).
* The second will be, afaik, the tightest known bound for ReLU networks.

**16.1**: **First covering number bound: Lipschitz functions**

This bound is intended as a point of contrast with our deep network generalization bounds.

**Theorem 16.1**: Let data \(S=(x_{1},\ldots,x_{n})\) be given with \(R:=\max_{i,j}\|x_{i}-x_{j}\|_{\infty}\). Let \(\mathcal{F}\) denote all \(\rho\)-Lipschitz functions from \([-R,+R]^{d}\to[-B,+B]\) (where Lipschitz is measured wrt \(\|\cdot\|_{\infty}\)). Then the **improper** covering number \(\widetilde{\mathcal{N}}\) satisfies

$$\ln\widetilde{\mathcal{N}}(\mathcal{F},\epsilon,\|\cdot\|_{\mathrm{u}})\leq \max\left\{0,\left\lceil\frac{4\rho(R+\epsilon)}{\epsilon}\right\rceil^{d}\ln \left\lceil\frac{2B}{\epsilon}\right\rceil\right\}.$$

**Remark 16.1**: Exponential in dimension!

Revisiting the "point of contrast" comment above, our deep network generalization bounds are polynomial and not exponential in dimension; consequently, we really are doing much better than simply treating the networks as arbitrary Lipschitz functions.

**Proof.**

* Suppose \(B>\epsilon\), otherwise can use the trivial cover \(\{x\mapsto 0\}\).
* Subdivide \([-R-\epsilon,+R+\epsilon]^{d}\) into \(\left(\frac{4(R+\epsilon)\rho}{\epsilon}\right)^{d}\) cubes of side length \(\frac{\epsilon}{2\rho}\); call this \(U\).
* Subdivide \([-B,+B]\) into intervals of length \(\epsilon\), thus \(2B/\epsilon\) elements; call this \(V\).
* Our candidate cover \(\mathcal{G}\) is the set of all piecewise constant maps from \([-R-\epsilon,+R+\epsilon]^{d}\) to \([-B,+B]\) discretized according to \(U\) and \(V\), meaning $$|\mathcal{G}|\leq\left\lceil\frac{2B}{\epsilon}\right\rceil^{\left\lceil\frac{ 4(R+\epsilon)\rho}{\epsilon}\right\rceil^{d}}.$$ To show this is an improper cover, given \(f\in\mathcal{F}\), choose \(g\in\mathcal{G}\) by proceeding over each \(C\in U\), and assigning \(g_{|C}\in V\) to be the closest element to \(f(x_{C})\), where \(x_{C}\) is the midpoint of \(C\). Then $$\|f-g\|_{\mathrm{u}} =\sup_{C\in U}\sup_{x\in C}|f(x)-g(x)|$$ $$\leq\sup_{C\in U}\sup_{x\in C}\left(|f(x)-f(x_{C})|+|f(x_{C})-g( x)|\right)$$ $$\leq\sup_{C\in U}\sup_{x\in C}\left(\rho\|x-x_{C}\|_{\infty}+ \frac{\epsilon}{2}\right)$$ $$\leq\sup_{C\in U}\sup_{x\in C}\left(\rho(\epsilon/(4\rho))+\frac {\epsilon}{2}\right)\leq\epsilon$$

[ mjt(r): hmm the proof used uniform norm... is it defined?]

**Theorem 16.2**: _(P. Bartlett, Foster, and Telgarsky (2017))_Fix _multivariate_ activations \((\sigma_{i})_{i=1}^{L}\) with \(\|\sigma\|_{\mathrm{Lip}}=:\rho_{i}\) and \(\sigma_{i}(0)=0\), and data \(X\in\mathbb{R}^{n\times d}\), and define

$$\mathcal{F}_{n}:=\Bigg{\{}\sigma_{L}(W_{L}\sigma_{L-1}\cdots\sigma_{1}(W_{1}X^ {\mathsf{T}})\cdots)\ :\ \|W_{i}^{\mathsf{T}}\|_{2}\leq s_{i},\|W_{i}^{\mathsf{T}}\|_{ 2,1}\leq b_{i}\Bigg{\}},$$

and all matrix dimensions are at most \(m\). Then

$$\ln\mathcal{N}\left(\mathcal{F}_{n},\epsilon,\|\cdot\|_{\mathrm{F}}\right)\leq \frac{\|X\|_{\mathrm{F}}^{2}\prod_{j=1}^{L}\rho_{j}^{2}s_{j}^{2}}{\epsilon^{2} }\left(\sum_{i=1}^{L}\left(\frac{b_{i}}{s_{i}}\right)^{2/3}\right)^{3}\ln(2m^ {2}).$$

**Remark 16.2**: Applying Dudley,

$$\mathrm{URad}(\mathcal{F}_{n})=\widetilde{\mathcal{O}}\left(\|X\|_{\mathrm{F} }\left[\prod_{j=1}^{L}\rho_{j}s_{j}\right]\cdot\left[\sum_{i=1}^{L}\left( \frac{b_{i}}{s_{i}}\right)^{2/3}\right]^{3/2}\right).$$

[ mir((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((())))((((((((((((((((((((((())))(((((((((((((((((()))))(((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((())))((((((((((((((())))((((((((())))((((((((()))(((((()))((((((()))(((((())(((())(((())(((())((()(()(()(()(()(()(()(()(()(()(()(()(()(()(()(()(()(()(()(()(()(()(()(()(()(()()(()(()(()(()(()(()(()()(()(()(()(()()(()(()()(()(()(()()(()(()()(()(()()(()()(()(()()(()()(()(()()(()()(()()(()()(()()(()()(()()()(()()(()()()(()()(()()()(()()()(()()()(()()()(()()()()(()()()()()(()()()()()()()()(()()()()()()()()()()()()()(()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()()())(())(())(())(())()()()()()()()()()()()()()()())(())(())(())()()()()()()()())(())(())(())(())(())())(())(())(())(())()())(())(())())(())(())(())()()())(())(())())(())(())()()())(())()()()()())()()())()())()()()())()()()())()()())()()())()()())()()())()()())()()())()()()())()()())()()()())()()())()()())()()())()())()()()())()()()()()()())()()())()()())()()()())()()())()()()())()()()()()())()())()()())()()())()()())()()())()()())()()()()()()()())()()())()()())()()()()()())()()()()()())()()())()()()()())()()()()()())()()()())()()()()())()()()())()()()()())()()()())()()()()()())()()())()()()())()()()()()()())()()()()())()()()())()()()())()()()()())()()()()()()())()()()())()()()()()())()()()())()()()()()())()()()())()()()())()()()()())()()()()())()()()())()()()()())()()()()()())()()()()()())()()()())()()()()())()()()()()())()()()()()())()()()()()())()()()()())()()()()())()()()()()())()()()()())()()()()())()()()()())()()()()())()()()()()()()())()()()()()())()()()()())()()()()()())()()()()()())()()()()()())()()()()()())()()()()()()()())()()()()()())()()()()()()()())()()()()()())()()()())()()())()()()()()()()()()())()()()()()())()()()()())()()()()())()()()()()()())()()()()()()())()()()()()()()()())()()()())()()()()()())()()()()()()())()()()()()()()()())()()()()()())()()()())()()()())()()()()()())()()()()())()()()())()()()())()()()()())()()()()()()())()()()()()())()()()())()()()()())()()()()()())()()())()()())()()()()())()()()()()())()()()()())()()()())()()()()()())()()()()()())()()()())()()()()())()()())()()())()()()()()()())()()()())()()()())()()()())()()()())()()())()()()()())()()()()())()()()()()()())()()()()()())()()())()()()()())()())()()()()())()()()()()()())()()())()()()())()()()()())()()())()()()())()()()())()()()())()()()()())()()()()())()()()()())()()())()()()())()()()()()())()()()()())()()())()())()()()())()()())()()()())()()())()()()())()()())()()())()())()()())()()()())()()())()()())()()()()())()()()())()()())()()()())()())()()())()()()())()()()())()())()()())()()())()()()())()()())()())()())()()()())()())()()())()())()()))The first step of the proof is a covering number for individual layers.

**Lemma 16.1**

$$\ln\mathcal{N}(\{WX^{\mathsf{T}}:X\in\mathbb{R}^{m\times d},\|W^{\mathsf{T}}\|_{2,1 }\leq b\},\epsilon,\|\cdot\|_{\mathrm{F}})\leq\left\lceil\frac{\|X\|_{\mathrm{F }}^{2}b^{2}}{\epsilon^{2}}\right\rceil\ln(2dm).$$

**Proof.** Let \(W\in\mathbb{R}^{m\times d}\) be given with \(\|W^{\mathsf{T}}\|_{2,1}\leq r\). Define \(s_{ij}:=W_{ij}/|W_{ij}|\), and note

$$WX^{\mathsf{T}}=\sum_{i,j}\mathbf{e}_{i}\mathbf{e}_{i}^{\mathsf{T}}W\mathbf{e}_ {j}\mathbf{e}_{j}^{\mathsf{T}}X^{\mathsf{T}}=\sum_{i,j}\mathbf{e}_{i}W_{ij}(X \mathbf{e}_{j})^{\mathsf{T}}=\sum_{i,j}\underbrace{\frac{|W_{ij}|\|X\mathbf{e} _{j}\|_{2}}{r\|X\|_{\mathrm{F}}}}_{=:q_{ij}}\underbrace{\frac{r\|X\|_{ \mathrm{F}}s_{ij}\mathbf{e}_{i}(X\mathbf{e}_{j})^{\mathsf{T}}}{\|X\mathbf{e} _{j}\|}}_{=:U_{ij}}.$$

Note by Cauchy-Schwarz that

$$\sum_{i,j}q_{ij}\leq\frac{1}{r\|X\|_{\mathrm{F}}}\sum_{i}\sqrt{\sum_{j}W_{ij}^ {2}}\|X\|_{\mathrm{F}}=\frac{\|W^{\mathsf{T}}\|_{2,1}\|X\|_{\mathrm{F}}}{r\|X \|_{\mathrm{F}}}\leq 1,$$

potentially with strict inequality, thus \(q\) is not a probability vector, which we will want later. To remedy this, construct probability vector \(p\) from \(q\) by adding in, with equal weight, some \(U_{ij}\) and its negation, so that the above summation form of \(WX^{\mathsf{T}}\) goes through equally with \(p\) as with \(q\). Now define IID random variables \((V_{1},\ldots,V_{k})\), where

$$\Pr[V_{l}=U_{ij}] =p_{ij},$$ $$\mathbb{E}\,V_{l} =\sum_{i,j}p_{ij}U_{ij}=\sum_{i,j}q_{ij}U_{ij}=WX^{\mathsf{T}},$$ $$\|U_{ij}\| =\left\|\frac{s_{ij}\mathbf{e}_{i}(X\mathbf{e}_{j})}{\|X\mathbf{e }_{j}\|_{2}}\right\|_{\mathrm{F}}\cdot r\|X\|_{\mathrm{F}}=|s_{ij}|\cdot\| \mathbf{e}_{i}\|_{2}\cdot\left\|\frac{X\mathbf{e}_{j}}{\|X\mathbf{e}_{j}\|_{2} }\right\|_{2}\cdot r\|X\|_{\mathrm{F}}=r\|X\|_{\mathrm{F}},$$ $$\mathbb{E}\,\|V_{l}\|^{2} =\sum_{i,j}p_{ij}\|U_{ij}\|^{2}\leq\sum_{ij}p_{ij}r^{2}\|X\|_{ \mathrm{F}}^{2}=r^{2}\|X\|_{\mathrm{F}}^{2}.$$

By +Lemma 3.1 (Maurey (Pisier 1980)), there exist \((\hat{V}_{1},\ldots,\hat{V}_{k})\in S^{k}\) with

$$\left\|WX^{\mathsf{T}}-\frac{1}{k}\sum_{l}\hat{V}_{l}\right\|^{2}\leq\mathbb{E }\left\|\mathbb{E}\,V_{1}-\frac{1}{k}\sum_{l}V_{l}\right\|^{2}\leq\frac{1}{k} \,\mathbb{E}\,\|V_{1}\|^{2}\leq\frac{r^{2}\|X\|_{\mathrm{F}}^{2}}{k}.$$

Furthermore, the matrices \(\hat{V}_{l}\) have the form

$$\frac{1}{k}\sum_{l}\hat{V}_{l}=\frac{1}{k}\sum_{l}\frac{s_{l}\mathbf{e}_{i_{l}} (X\mathbf{e}_{j_{l}})^{\mathsf{T}}}{\|X\mathbf{e}_{j_{l}}\|}=\left[\frac{1}{k} \sum_{l}\frac{s_{l}\mathbf{e}_{i_{l}}\mathbf{e}_{j_{l}}^{\mathsf{T}}}{\|X \mathbf{e}_{j_{l}}\|}\right]X^{\mathsf{T}};$$

by this form, there are at most \(\left(2nd\right)^{k}\) choices for \((\hat{V}_{1},\ldots,\hat{V}_{k})\).

**Lemma 16.2** Let \(\mathcal{F}_{n}\) be the same image vectors as in the theorem, and let per-layer tolerances \((\epsilon_{1},\ldots,\epsilon_{L})\) be given. then

$$\ln\mathcal{N}\left(\mathcal{F}_{n},\ \sum_{j=1}^{L}\rho_{j}\epsilon_{j}\prod_{k=j+1}^ {L}\rho_{k}s_{k},\ \|\cdot\|_{\mathrm{F}}\right)\leq\sum_{i=1}^{L}\left\lceil\frac{\|X\|_{ \mathrm{F}}^{2}b_{i}^{2}\prod_{j<i}\rho_{j}^{2}s_{j}^{2}}{\epsilon_{i}^{2}} \right\rceil\ln(2m^{2}).$$

**Proof.** Let \(X_{i}\) denote the output of layer \(i\) of the network, using weights \((W_{i},\ldots,W_{1})\), meaning

$$X_{0}:=X\qquad\text{and}\qquad X_{i}:=\sigma_{i}(X_{i-1}W_{i}^{\intercal}).$$

The proof recursively constructs cover elements \(\hat{X}_{i}\) and weights \(\hat{W}_{i}\) for each layer with the following basic properties.

* Define \(\hat{X}_{0}:=X_{0}\), and \(\hat{X}_{i}:=\Pi_{B_{i}}\sigma_{i}(\hat{X}_{i-1}\hat{W}_{i}^{\intercal})\), where \(B_{i}\) is the Frobenius-norm ball of radius \(\|X\|_{\mathrm{F}}\prod_{j<i}\rho_{j}s_{j}\).
* Due to the projection \(\Pi_{B_{i}}\), \(\|\hat{X}_{i}\|_{\mathrm{F}}\leq\|X\|_{\mathrm{F}}\prod_{j\leq i}\rho_{j}s_{j}\). Similarly, using \(\rho_{i}(0)=0\), \(\|X_{i}\|_{\mathrm{F}}\leq\|X\|_{\mathrm{F}}\prod_{j<i}\rho_{j}s_{j}\).
* Given \(\hat{X}_{i-1}\), choose \(\hat{W}_{i}\) via \(+\)Lemma 16.1 so that \(\|\hat{X}_{i-1}W_{i}^{\intercal}-\hat{X}_{i-1}\hat{W}_{i}^{\intercal}\|_{ \mathrm{F}}\leq\epsilon_{i}\), whereby the corresponding covering number \(\mathcal{N}_{i}\) for this layer satisfies $$\ln\mathcal{N}_{i}\leq\left\lceil\frac{\|\hat{X}_{i-1}\|_{\mathrm{F}}^{2}b_{i }^{2}}{\epsilon_{i}^{2}}\right\rceil\ln(2m^{2})\leq\left\lceil\frac{\|X\|_{ \mathrm{F}}^{2}b_{i}^{2}\prod_{j<i}\rho_{j}^{2}s_{j}^{2}}{\epsilon_{i}^{2}} \right\rceil\ln(2m^{2}).$$
* Since each cover element \(\hat{X}_{i}\) depends on the full tuple \((\hat{W}_{i},\ldots,\hat{W}_{1})\), the final cover is the product of the individual covers (and not their union), and the final cover log cardinality is upper bounded by $$\ln\prod_{i=1}^{L}\mathcal{N}_{i}\leq\sum_{i=1}^{L}\left\lceil\frac{\|X\|_{ \mathrm{F}}^{2}b_{i}^{2}\prod_{j<i}\rho_{j}^{2}s_{j}^{2}}{\epsilon_{i}^{2}} \right\rceil\ln(2m^{2}).$$

It remains to prove, by induction, an error guarantee

$$\|X_{i}-\hat{X}_{i}\|_{\mathrm{F}}\leq\sum_{j=1}^{i}\rho_{j}\epsilon_{j}\prod _{k=j+1}^{i}\rho_{k}s_{k}.$$

The base case \(\|X_{0}-\hat{X}_{0}\|_{\mathrm{F}}=0=\epsilon_{0}\) holds directly. For the inductive step, by the above ingredients and the triangle inequality,

$$\|X_{i}-\hat{X}_{i}\|_{\mathrm{F}} \leq\rho_{i}\|X_{i-1}W_{i}^{\intercal}-\hat{X}_{i-1}\hat{W}_{i}^{ \intercal}\|_{\mathrm{F}}$$ $$\leq\rho_{i}\|X_{i-1}W_{i}^{\intercal}-\hat{X}_{i-1}W_{i}^{ \intercal}\|_{\mathrm{F}}+\rho_{i}\|\hat{X}_{i-1}W_{i}^{\intercal}-\hat{X}_{i- 1}\hat{W}_{i}^{\intercal}\|_{\mathrm{F}}$$ $$\leq\rho_{i}s_{i}\|X_{i-1}-\hat{X}_{i-1}\|_{\mathrm{F}}+\rho_{i} \epsilon_{i}$$ $$\leq\rho_{i}s_{i}\left[\sum_{j=1}^{i-1}\rho_{j}\epsilon_{j}\prod _{k=j+1}^{i-1}\rho_{k}s_{k}\right]+\rho_{i}\epsilon_{i}$$ $$=\left[\sum_{j=1}^{i-1}\rho_{j}\epsilon_{j}\prod_{k=j+1}^{i}\rho_ {k}s_{k}\right]+\rho_{i}\epsilon_{i}$$ $$=\sum_{j=1}^{i}\rho_{j}\epsilon_{j}\prod_{k=j+1}^{i}\rho_{k}s_{k}.$$

**Proof of \(+\)Theorem 16.2 (P. Bartlett, Foster, and Telgarsky (2017)).** By solving aLagrangian (minimize cover size subject to total error \(\leq\epsilon\)), choose

$$\epsilon_{i}:=\frac{\alpha_{i}\epsilon}{\rho_{i}\prod_{j>i}\rho_{j}s_{j}},\qquad \alpha_{i}:=\frac{1}{\beta}\left(\frac{b_{i}}{s_{i}}\right)^{2/3},\qquad\beta:= \sum_{i=1}^{L}\left(\frac{b_{i}}{s_{i}}\right)^{2/3}.$$

Invoking the induction lemma with these choices, the resulting cover error is

$$\sum_{i=1}^{L}\epsilon_{i}\rho_{i}\prod_{j>i}\rho_{j}s_{j}=\epsilon\sum_{j=1}^{ L}\alpha_{i}=\epsilon.$$

and the main term of the cardinality (ignoring \(\ln(2m^{2})\)) satisfies

$$\sum_{i=1}^{L}\frac{\|X\|_{\rm F}^{2}b_{i}^{2}\prod_{j<i}\rho_{j} ^{2}s_{j}^{2}}{\epsilon_{i}^{2}}=\frac{\|X\|_{\rm F}^{2}}{\epsilon^{2}}\sum_{ i=1}^{L}\frac{b_{i}^{2}\prod_{j=1}^{L}\rho_{j}^{2}s_{j}^{2}}{\alpha_{i}^{2}s_{ i}^{2}}$$ $$=\frac{\|X\|_{\rm F}^{2}\prod_{j=1}^{L}\rho_{j}^{2}s_{j}^{2}}{ \epsilon^{2}}\sum_{i=1}^{L}\frac{\beta^{2}b_{i}^{2/3}}{s_{i}^{2/3}}=\frac{\|X \|_{\rm F}^{2}\prod_{j=1}^{L}\rho_{j}^{2}s_{j}^{2}}{\epsilon^{2}}\left(\sum_{i =1}^{L}\left(\frac{b_{i}}{s_{i}}\right)^{2/3}\right)^{3}.$$

[ mjt(r): I should include the Lagrangian explicitly and also explicit Dudley.]

[ mjt(r): I should include in preamble various bounds not taught, and a comment that VC dim proofs are interesting and reveal structure not captured above.]

* VC dimension is an ancient generalization technique; essentially the quantity itself appears in the work of Kolmogorov, and was later rediscovered a few times, and named after Vapnik and Chervonenkis, whose used it for generalization.
* To prove generalization, we will upper bound Rademacher complexity with VC dimension; classical VC dimension generalization proofs include Rademacher averages.
* There is some huge ongoing battle of whether VC dimension is a good measure or not. I think the proofs are interesting and are sensitive to interesting properties of deep networks in ways not capture by many of the bounds we spent time on. Anyway, a discussion for another time...
* As stated the bounds are worst-case-y; I feel they could be adapted into more average-case-y bounds, though this has not been done yet...

First, some definitions. First, the zero-one/classification risk/error:

$${\cal R}_{\rm z}({\rm sgn}(f))={\rm Pr}[{\rm sgn}(f(X))\neq Y],\ \widehat{ \cal R}_{\rm z}({\rm sgn}(f))=\frac{1}{n}\sum_{i=1}^{n}{\bf 1}[{\rm sgn}(f(x_{i})) \neq y_{i}].$$The earlier Rademacher bound will now have

$$\text{URad}\left(\{(x,y)\mapsto\mathbf{1}[\text{sgn}(f(x))\neq y]:f\in\mathcal{F} \}_{|S}\right).$$

This is at most \(2^{n}\); we'll reduce it to a combinatorial quantity:

$$\text{sgn}(U) :=\left\{(\text{sgn}(u_{1}),\ldots,\text{sgn}(u_{n})):u\in V \right\},$$ $$\text{Sh}(\mathcal{F}_{|S}) :=\left|\text{sgn}(\mathcal{F}_{|S})\right|,$$ $$\text{Sh}(\mathcal{F};n) :=\sup_{\begin{subarray}{c}S\in\mathcal{T}\\ |S|\leq n\end{subarray}}\left|\text{sgn}(\mathcal{F}_{|S})\right|,$$ $$\text{VC}(\mathcal{F}) :=\sup\{i\in\mathbb{Z}_{\geq 0}:\text{Sh}(\mathcal{F};i)=2^{i}\}.$$

**Remark 17.1**: Sh is "shatter coefficient," VC is "VC dimension."

Both quantities are criticized as being too tied to their worst case; bounds here depend on (empirical quantity!) \(\text{URad}(\text{sgn}(\mathcal{F}_{|S}))\), which can be better, but throws out the labels.
**Theorem 17.1** ("VC Theorem"): _With probability at least \(1-\delta\), every \(f\in\mathcal{F}\) satisfies_

$$\mathcal{R}_{\text{z}}(\text{sgn}(f))\leq\widehat{\mathcal{R}}_{\text{z}}( \text{sgn}(f)+\frac{2}{n}\text{URad}(\text{sgn}(\mathcal{F}_{|S}))+3\sqrt{ \frac{\ln(2/\delta)}{2n}},$$

_and_

$$\text{URad}(\text{sgn}(\mathcal{F}_{|S})) \leq\sqrt{2n\ln\text{Sh}(\mathcal{F}_{|S})},$$ $$\ln\text{Sh}(\mathcal{F}_{|S}) \leq\ln\text{Sh}(\mathcal{F};n)\leq\text{VC}(\mathcal{F})\ln(n+1).$$

**Remark 17.2**: [ mjt(r): Say something like "Need \(\text{Sh}(\mathcal{F}_{|s})=o(n)\)"in order to learn":?]

Minimizing \(\widehat{\mathcal{R}}_{\text{z}}\) is NP-hard in many trivial cases, but those require noise and neural networks can often get \(\widehat{\mathcal{R}}_{\text{z}}(\text{sgn}(f))=0\).

\(\text{VC}(\mathcal{F})<\infty\) suffices; many considered this a conceptual breakthrough, namely "learning is possible!"

The quantities (VC, Sh) appeared in prior work (not by V-C). Symmetrization apparently too, though I haven't dug this up.

First step of proof: pull out the zero-one loss.

**Lemma 17.1**: \(\text{URad}(\{(x,y)\mapsto\mathbf{1}[\text{sgn}(f(x))\neq y]:f\in\mathcal{F} \}_{|S})\leq\text{URad}(\text{sgn}(\mathcal{F}_{|S})).\)__

**Proof.** For each \(i\), define

$$\ell_{i}(z):=\max\left\{0,\min\left\{1,\frac{1-y_{i}(2z-1)}{2}\right\}\right\},$$

which is 1-Lipschitz, and satisfies

$$\ell_{i}(\text{sgn}(f(x_{i})))=\mathbf{1}[\text{sgn}(f(x_{i}))\neq y_{i}].$$(Indeed, it is the linear interpolation.) Then

$$\begin{array}{l}\mbox{URad}(\{(x,y)\mapsto{\bf 1}[\mbox{sgn}(f(x))\neq y]:f\in{ \cal F}\}_{|S})\\ =\mbox{URad}(\{(\ell_{1}(\mbox{sgn}(f(x_{1}))),\ldots,\ell_{n}(\mbox{sgn}(f(x_{n} )))):f\in{\cal F}\}_{|S})\\ =\mbox{URad}(\ell\circ\mbox{sgn}({\cal F})_{|S})\\ \leq\mbox{URad}(\mbox{sgn}({\cal F})_{|S}).\end{array}$$

[ mjt(r): is that using the fancier per-coordinate vector-wise peeling again?]

Plugging this into our Rademacher bound: \(\mbox{w/ pr}\geq 1-\delta\), \(\forall f\in{\cal F}\),

$${\cal R}_{\sf z}(\mbox{sgn}(f))\leq\widehat{\cal R}_{\sf z}(\mbox{sgn}(f))+ \frac{2}{n}\mbox{URad}(\mbox{sgn}({\cal F})_{|S})+3\sqrt{\frac{\ln(2/\delta)}{ 2n}}.$$

The next step is to apply Massart's finite lemma, giving

$$\mbox{URad}(\mbox{sgn}({\cal F}_{|S}))\leq\sqrt{2n\mbox{Sh}({\cal F}_{|S})}.$$

One last lemma remains for the proof.

[ mjt(r): lol why mention warren. should be explicit and not passive-aggressive.]

[**Lemma 17.2**: _(Sauer-Shelah? Vapnik-Chervonenkis? Warren?...)_] Let \({\cal F}\) be given, and define \(V:=\mbox{VC}({\cal F})\). Then

$$\mbox{Sh}({\cal F};n)\leq\begin{cases}2^{n}&\mbox{when $n\leq V$,}\\ \big{(}\frac{en}{V}\big{)}^{V}&\mbox{otherwise.}\end{cases}$$

Moreover, \(\mbox{Sh}({\cal F};n)\leq n^{V}+1\).

[**Proof.** Omitted. Exists in many standard texts.]

[ mjt(r): okay fine but i should give a reference, and eventually my own clean proof.]

[**Theorem 17.2**: Define \({\cal F}:=\Big{\{}x\mapsto\mbox{sgn}(\langle a,x\rangle-b):a\in\mathbb{R}^{d },b\in\mathbb{R}\Big{\}}\) ("linear classifiers"/"affine classifier"/ "linear threshold function (LTF)"). Then \(\mbox{VC}({\cal F})=d+1\).
**Remark 17.3**: By Sauer-Shelah, \(\mbox{Sh}({\cal F};n)\leq n^{d+1}+1\). Anthony-Bartlett chapter 3 gives an exact equality; only changes constants of \(\ln\mbox{VC}({\cal F};n)\).

Let's compare to Rademacher:

$$\begin{array}{l}\mbox{URad}(\mbox{sgn}({\cal F}_{|S}))\leq\sqrt{2nd\ln(n+1) },\\ \mbox{URad}(\{x\mapsto\langle w,x\rangle:\|w\|\leq R\}_{|S})\leq R\|X_{S}\|_{F},\end{array}$$

where \(\|X_{S}\|_{F}^{2}=\sum_{x\in S}\|x\|_{2}^{2}\leq n\cdot d\cdot\max_{i,j}x_{i,j}\). One is scale-sensitive (and suggests regularization schemes), other is scale-insensitive.

**Proof**. First let's do the lower bound \(\operatorname{VC}(\mathcal{F})\geq d+1\).

* Suffices to show \(\exists S:=\{x_{1},\ldots,x_{d+1}\}\) with \(\operatorname{Sh}(\mathcal{F}_{|S})=2^{d+1}\).
* Choose \(S:=\{\mathbf{e}_{1},\ldots,\mathbf{e}_{d},(0,\ldots,0)\}\).

Given any \(P\subseteq S\), define \((a,b)\) as

$$a_{i}:=2\cdot\mathbf{1}[\mathbf{e}_{i}\in P]-1,\qquad b:=\frac{1}{2}-\mathbf{1 }[0\in P].$$

Then

$$\operatorname{sgn}(\langle a,\mathbf{e}_{i}\rangle-b) =\operatorname{sgn}(2\mathbf{1}[\mathbf{e}_{i}\in P]-1-b)=2 \mathbf{1}[\mathbf{e}_{i}\in P]-1,$$ $$\operatorname{sgn}(\langle a,0\rangle-b) =\operatorname{sgn}(2\mathbf{1}[0\in P]-1/2)=2\mathbf{1}[0\in P ]-1,$$

meaning this affine classifier labels \(S\) according to \(P\), which was an arbitrary subset.

Now let's do the upper bound \(\operatorname{VC}(\mathcal{F})<d+2\).

* Consider any \(S\subseteq\mathbb{R}^{d}\) with \(|S|=d+2\).
* By _Radon's Lemma_ (proved next), there exists a partition of \(S\) into nonempty \((P,N)\) with \(\operatorname{conv}(P)\cap\operatorname{conv}(N)\).
* Label \(P\) as positive and \(N\) as negative. Given any affine classifier, it can not be correct on all of \(S\) (and thus \(\operatorname{VC}(\mathcal{F})<d+2\)): either it is incorrect on some of \(P\), or else it is correct on \(P\), and thus has a piece of \(\operatorname{conv}(N)\) and thus \(x\in N\) labeled positive.

[ mjt(c): needs ref]

**Lemma 17.3**_(Radon's Lemma)_: Given \(S\subseteq\mathbb{R}^{d}\) with \(|S|=d+2\), there exists a partition of \(S\) into nonempty \((P,N)\) with \(\operatorname{conv}(P)\cap\operatorname{conv}(S)\neq\emptyset\).

**Proof.** Let \(S=\{x_{1},\ldots,x_{d+2}\}\) be given, and define \(\{u_{1},\ldots,u_{d+1}\}\) as \(u_{i}:=x_{i}-x_{d+2}\), which must be linearly dependent:

* Exist scalars \((\alpha_{1},\ldots,\alpha_{d+1})\) and a \(j\) with \(\alpha_{j}:=-1\) so that $$\sum_{i}\alpha_{i}u_{i}=-u_{j}+\sum_{i\neq j}\alpha_{i}u_{i}=0;$$
* thus \(x_{j}-x_{d+2}=\sum\limits_{\begin{subarray}{c}i\neq j\\ i<d+2\end{subarray}}\alpha_{i}(x_{i}-x_{d+2})\) and \(0=\sum_{i<d+2}\alpha_{i}x_{i}-x_{d+2}\sum_{i<d+2}\alpha_{i}=:\sum_{j}\beta_{j} x_{j}\), where \(\sum_{j}\beta_{j}=0\) and not all \(\beta_{j}\) are zero.

Set \(P:=\{i:\beta_{i}>0\}\), \(N:=\{i:\beta_{i}\leq 0\}\); where neither set is empty.

Set \(\beta:=\sum_{i\in P}\beta_{i}-\sum_{i\in N}\beta_{i}>0\).

Since \(0=\sum_{i}\beta_{i}x_{i}=\sum_{i\in P}\beta_{i}x_{i}+\sum_{i\in N}\beta_{i}x_{i}\), then

$$\frac{0}{\beta}=\sum_{i\in P}\frac{\beta_{i}}{\beta}x_{i}+\sum_{i\in N}\frac{ \beta_{i}}{\beta}x_{i}$$

and the point \(z:=\sum_{i\in P}\beta_{i}x_{i}/\beta=\sum_{i\in N}\beta_{i}x_{i}/(-\beta)\) satisfies \(z\in\operatorname{conv}(P)\cap\operatorname{conv}(N)\).

**Remark 17.4**: Generalizes Minsky-Papert "xor" construction.

Indeed, the first appearance I know of shattering/VC was in approximation theory, the papers of Warren and Shapiro, and perhaps it is somewhere in Kolmogorov's old papers.

**17.2**: **VC dimension of threshold networks**Consider iterating the previous construction, giving an "LTF network": a neural network with activation \(z\mapsto\mathbf{1}[z\geq 0]\).

We'll analyze this by studying output of all nodes. To analyze this, we'll study not just the outputs, but the behavior of all nodes.

[ mjt(c): another suggestion of definition in pandoc-numbering]

**Definition.**

* Given a sample \(S\) of size \(n\) and an LTF network with \(m\) nodes (in any topologically sorted order), define activation matrix \(A:=\operatorname{Act}(S;W:=(a_{1},\ldots,a_{m}))\) where \(A_{ij}\) is the output of node \(j\) on input \(i\), with fixed network weights \(W\).
* Let \(\operatorname{Act}(S;\mathcal{F})\) denote the set of activation matrices with architecture fixed and weights \(W\) varying.

**Remark 17.5**: Since last column is the labeling, \(|\operatorname{Act}(S;\mathcal{F})|\geq\operatorname{Sh}(\mathcal{F}_{|S})\).

Act seems a nice complexity measure, but it is hard to estimate given a single run of an algorithm (say, unlike a Lipschitz constant).

We'll generalize Act to analyze ReLU networks.

**Theorem 17.3**: For any LTF architecture \(\mathcal{F}\) with \(p\) parameters,

$$\operatorname{Sh}(\mathcal{F};n)\leq|\operatorname{Act}(S;\mathcal{F})|\leq(n +1)^{p}.$$

When \(p\geq 12\), then \(\operatorname{VC}(\mathcal{F})\leq 6p\ln(p)\).

**Proof.**

* Topologically sort nodes, let \((p_{1},\ldots,p_{m})\) denote numbers of respective numbers of parameters (thus \(\sum_{i}p_{i}=p\)).
* Proof will iteratively construct sets \((U_{1},\ldots,U_{m})\) where \(U_{i}\) partitions the weight space of nodes \(j\leq i\) so that, within each partition cell, the activation matrix does not vary.
* The proof will show, by induction, that \(|U_{i}|\leq(n+1)^{\sum_{j\leq i}p_{j}}\). This completes the proof of the first claim, since \(\operatorname{Sh}(\mathcal{F}_{|S})\leq|\operatorname{Act}(\mathcal{F};S)|=|U_{m}|\).
* For convenience, define \(U_{0}=\{\emptyset\}\), \(|U_{0}|=1\); the base case is thus \(|U_{0}|=1=(n+1)^{0}\).
**(Inductive step).** Let \(j\geq 1\) be given; the proof will now construct \(U_{j+1}\) by refining the partition \(U_{j}\).

* Fix any cell \(C\) of \(U_{j}\); as these weights vary, the activation is fixed, thus the input to node \(j+1\) is fixed for each \(x\in S\).
* Therefore, on this augmented set of \(n\) inputs (\(S\) with columns of activations appended to each example), there are \((n+1)^{p_{j+1}}\) possible outputs via Sauer-Shelah and the VC dimension of affine classifiers with \(p_{j+1}\) inputs.
* In other words, \(C\) can be refined into \((n+1)^{p_{j+1}}\) sets; since \(C\) was arbitrary, $$|U_{j+1}|=|U_{j}|(n+1)^{p_{j+1}}\leq(n+1)^{\sum_{l\leq j+1}p_{l}}.$$ This completes the induction and establishes the Shattering number bound.

It remains to bound the VC dimension via this Shatter bound:

$$\begin{split}&\text{VC}(\mathcal{F})<n\\ \Longleftrightarrow&\forall i\geq n\centerdot\text{Sh}( \mathcal{F};i)<2^{i}\\ \Longleftrightarrow&\forall i\geq n\centerdot(i+1)^{p }<2^{i}\\ \Longleftrightarrow&\forall i\geq n\centerdot p\ln(i+1 )<i\ln 2\\ \Longleftrightarrow&\forall i\geq n\centerdot p< \frac{i\ln(2)}{\ln(i+1)}\\ \Longleftrightarrow& p<\frac{n\ln(2)}{\ln(n+1)}\end{split}$$

If \(n=6p\ln(p)\),

$$\begin{split}\frac{n\ln(2)}{\ln(n+1)}&\geq\frac{n \ln(2)}{\ln(2n)}=\frac{6p\ln(p)\ln(2)}{\ln 12+\ln p+\ln\ln p}\\ &\geq\frac{6p\ln p\ln 2}{3\ln p}>p.\end{split}$$

**Remark 17.6**: Had to do handle \(\forall i\geq n\) since VC dimension is defined via sup; one can define funky \(\mathcal{F}\) where Sh is not monotonic in \(n\).

Lower bound is \(\Omega(p\ln m)\); see Anthony-Bartlett chapter 6 for a proof. This lower bound however is for a specific fixed architecture!

Other VC dimension bounds: ReLU networks have \(\widetilde{\mathcal{O}}(pL)\), sigmoid networks have \(\widetilde{\mathcal{O}}(p^{2}m^{2})\), and there exists a convex-concave activation which is close to sigmoid but has VC dimension \(\infty\).

Matching lower bounds exist for ReLU, not for sigmoid; but even the "matching" lower bounds are deceptive since they hold for a _fixed_ architecture of a given number of parameters and layers.

**V****C dimension of ReLU networks**

Today's ReLU networks will predict with

$$x\mapsto A_{L}\sigma_{L-1}\left(A_{L-1}\cdots A_{2}\sigma_{1}(A_{1}x+b_{1})+b _{2}\cdots+b_{L-1}\right)+b_{L},$$

where \(A_{i}\in\mathbb{R}^{d_{i}\times d_{i-1}}\) and \(\sigma_{i}:\mathbb{R}^{d_{i}\to d_{i}}\) applies the ReLU \(z\mapsto\max\{0,z\}\) coordinate-wise.

**Convenient notation:** collect data as rows of matrix \(X\in\mathbb{R}^{n\times d}\), and define

$$\begin{split} X_{0}&:=X^{\top}\hskip 113.811024ptZ_{0} :=\text{all 1s matrix},\\ X_{i}&:=A_{i}(Z_{i-1}\odot X_{i-1})+b_{i}1_{n}^{ \top},\hskip 8.535827ptX_{i}:=\mathbf{1}[X_{i}\geq 0],\end{split}$$

where \((Z_{1},\ldots,Z_{L})\) are the activation matrices.

[ mjt(): i should double check i have the tightest version? which is more sensitive to earlier layers? i should comment on that and the precise structure/meaning of the lower bounds?]

**Theorem 17.4** ((Theorem 6, P. L. Bartlett et al. 2017)): _Let fixed ReLU architecture \(\mathcal{F}\) be given with \(p=\sum_{i=1}^{L}p_{i}\) parameters, \(L\) layers, \(m=\sum_{i=1}^{L}m_{i}\) nodes. Let examples \((x_{1},\ldots,x_{n})\)be given and collected into matrix \(X\). There exists a partition \(U_{L}\) of the parameter space satisfying:

* Fix any \(C\in U_{L}\). As parameters vary across \(C\), activations \((Z_{1},\ldots,Z_{L})\) are fixed.
* \(\mathrm{Sh}(\mathcal{F};n)\leq|\{Z_{L}(C):C\in U_{L}\}|\leq|U_{L}|\leq(12nL)^{ pL}\), where \(Z_{L}(C)\) denotes the sign pattern in layer \(L\) for \(C\in U_{L}\).
* If \(pL^{2}\geq 72\), then \(\mathrm{VC}(\mathcal{F})\leq 6pL\ln(pL)\).

**Remark 17.7**: _(on the proof)_: As with LTF networks, the prove inductively constructs partitions of the weights up through layer \(i\) so that the activations are fixed across all weights in each partition cell.

Consider a fixed cell of the partition, whereby the activations are fixed zero-one matrices. As a function of the _inputs_, the ReLU network is now _an affine function_; as a function of the _weights_ it is _multilinear_ or rather _a polynomial of degree \(L\)_._

Consider again a fixed cell and some layer \(i\); thus \(\sigma(X_{i})=Z_{i}\odot X_{i}\) is a matrix of polynomials of degree \(i\) (in the weights). If we can upper bound the number of possible signs of \(A_{i+1}(Z_{i}\odot X_{i})+b_{i}1_{n}^{\top}\), then we can refine our partition of weight space and recurse. For that we need a bound on sign patterns of polynomials, as on the next slide.

**Theorem 17.5**: _(Warren '68; see also Anthony-Bartlet Theorem 8.3)_: Let \(F\) denote functions \(x\mapsto f(x;w)\) which are \(r\)-degree polynomials in \(w\in\mathbb{R}^{p}\). If \(n\geq p\), then \(\mathrm{Sh}(\mathcal{F};n)\leq 2(\frac{2enr}{p})^{p}\).
**Remark 17.8**: Proof is pretty intricate, and omitted. It relates the VC dimension of \(F\) to the zero sets \(Z_{i}:=\{w\in\mathbb{R}^{p}:f(x;w)=0\}\), which it controls with an application of Bezout's Theorem. The zero-counting technique is also used to obtain an exact Shatter coefficient for affine classifiers.

**Proof** (of ReLU VC bound).

We'll inductively construct partitions \((U_{0},\ldots,U_{L})\) where \(U_{i}\) partitions the parameters of layers \(j\leq i\) so that for any \(C\in U_{i}\), the activations \(Z_{j}\) in layer \(j\leq i\) are fixed for all parameter choices within \(C\) (thus let \(Z_{j}(C)\) denote these fixed activations).

The proof will proceed by induction, showing \(|U_{i}|\leq(12nL)^{pi}\).

**Base case \(i=0\)**: then \(U_{0}=\{\emptyset\}\), \(Z_{0}\) is all ones, and \(|U_{0}|=1\leq(12nL)^{pi}\).

**(Inductive step).**

* Fix \(C\in S_{i}\) and \((Z_{1},\ldots,Z_{i})=(Z_{1}(C),\ldots,Z_{i}(C))\).
* Note \(X_{i+1}=A_{i+1}(Z_{i}\odot X_{i})+b_{i}1_{n}^{\top}\) is polynomial (of degree \(i+1\)) in the parameters since \((Z_{1},\ldots,Z_{i})\) are fixed.
* Therefore $$|\{\mathbf{1}[X_{i+1}\geq 0]:\mathrm{params}\in C\}| \leq\mathrm{Sh}(i+1\text{ deg poly; }m_{i}\cdot n\text{ functions})$$ $$\leq 2\left(\frac{2enm_{i+1}}{\sum_{j\leq i}p_{j}}\right)^{\sum_ {j\leq i+1}p_{j}}\leq(12nL)^{p}.$$

[ Technical comment: to apply the earlier shatter bound for polynomials, we needed \(n\cdot m_{i+1}\geq\sum_{j}p_{j}\); but if (even more simply) \(p\geq nm_{i+1}\), we can only have \(\leq 2^{nm_{i+1}}\leq 2^{p}\) activation matrices anyway, so the bound still holds. ]* Therefore carving \(U_{i}\) into pieces according to \(Z_{i+1}=\mathbf{1}[X_{i+1}\geq 0]\) being fixed gives $$|U_{i+1}|\leq|U_{i}|(12nL)^{p}\leq(12nL)^{p(i+1)}.$$ This completes the induction and upper bounds the number of possible activation patterns and also the shatter coefficient.

It remains to upper bound the VC dimension via the Shattering bound. As with LTF networks,

$$\text{VC}(\mathcal{F})<n \Longleftrightarrow\forall i\geq n\centerdot\text{Sh}(\mathcal{F}; i)<2^{i}$$ $$\Longleftrightarrow\forall i\geq n\centerdot(12iL)^{pL}<2^{i}$$ $$\Longleftrightarrow\forall i\geq n\centerdot pL\ln(12iL)<i\ln 2$$ $$\Longleftrightarrow\forall i\geq n\centerdot pL<\frac{i\ln 2}{\ln(12iL)}$$ $$\Longleftrightarrow pL<\frac{n\ln 2}{\ln(12nL)}$$

If \(n=6pL\ln(pL)\),

$$\frac{n\ln 2}{\ln(12nL)} =\frac{6pL\ln(pL)\ln(2)}{\ln(72pL^{2}\ln(pL))}=\frac{6pL\ln(pL)\ln( 2)}{\ln(72)+\ln(pL^{2})+\ln\ln(pL)}$$ $$\geq\frac{6pL\ln(pL)\ln(2)}{\ln(72)+\ln(pL^{2})+\ln(pL)-1}\geq \frac{6\ln(pL)\ln(2)}{3\ln(pL^{2})}$$ $$=2pL\ln 2>pL.$$

**Remark 17.9**: If ReLU is replaced with a degree \(r\geq 2\) piecewise polynomial activation, have \(r^{i}\)-degree polynomial in each cell of partition, and shatter coefficient upper bound scales with \(L^{2}\) not \(L\). The lower bound in this case still has \(L\) not \(L^{2}\); it's not known where the looseness is.

Lower bounds are based on digit extraction, and for each pair \((p,L)\) require a fixed architecture.

## References

* [Allen-Zhu, Li, and Liang2019] Allen-Zhu, Zeyuan, and Yuanzhi Li. 2019. "What Can ResNet Learn Efficiently, Going Beyond Kernels?"
* [Allen-Zhu, Li, and Liang2018] Allen-Zhu, Zeyuan, Yuanzhi Li, and Yingyu Liang. 2018. "Learning and Generalization in Overparameterized Neural Networks, Going Beyond Two Layers." _arXiv Preprint arXiv:1811.04918_.
* [Allen-Zhu, Li, and Song2018] Allen-Zhu, Zeyuan, Yuanzhi Li, and Zhao Song. 2018. "A Convergence Theory for Deep Learning via over-Parameterization."
* [Arjovsky, Chintala, and Bottou2017] Arjovsky, Martin, Soumith Chintala, and Leon Bottou. 2017. "Wasserstein Generative Adversarial Networks." In _ICML_.
* [Arora, Cohen, Golowich, and Hu2018a] Arora, Sanjeev, Nadav Cohen, Noah Golowich, and Wei Hu. 2018a. "A Convergence Analysis of Gradient Descent for Deep Linear Neural Networks."
* [Arora, Cohen, Golowich, and Hu2018b] ------. 2018b. "A Convergence Analysis of Gradient Descent for Deep Linear Neural Networks."
* [Arora, Cohen, Golowich, and Hu2018a]Arora, Sanjeev, Nadav Cohen, and Elad Hazan. 2018. "On the Optimization of Deep Networks: Implicit Acceleration by Overparameterization." In _Proceedings of the 35th International Conference on Machine Learning_, edited by Jennifer Dy and Andreas Krause, 80:244-53. Proceedings of Machine Learning Research. Stockholmsmassan, Stockholm Sweden: PMLR. [http://proceedings.mlr.press/v80/arora18a.html](http://proceedings.mlr.press/v80/arora18a.html).
* [Arora et al.2019] Arora, Sanjeev, Nadav Cohen, Wei Hu, and Yuping Luo. 2019. "Implicit Regularization in Deep Matrix Factorization." In _Advances in Neural Information Processing Systems_, edited by H. Wallach, H. Larochelle, A. Beygelzimer, F. dAlche-Buc, E. Fox, and R. Garnett, 32:7413-24. Curran Associates, Inc. [https://proceedings.neurips.cc/paper/2019/file/c0c783b5fc0d7d808f1d14a6e9c8280d-Paper.pdf](https://proceedings.neurips.cc/paper/2019/file/c0c783b5fc0d7d808f1d14a6e9c8280d-Paper.pdf).
* [Arora et al.2019] Arora, Sanjeev, Simon S Du, Wei Hu, Zhiyuan Li, Ruslan Salakhutdinov, and Ruosong Wang. 2019. "On Exact Computation with an Infinitely Wide Neural Net." _arXiv Preprint arXiv:1904.11955_.
* [Arora et al.2019] Arora, Sanjeev, Simon S Du, Wei Hu, Zhiyuan Li, and Ruosong Wang. 2019. "Fine-Grained Analysis of Optimization and Generalization for Overparameterized Two-Layer Neural Networks." _arXiv Preprint arXiv:1901.08584_.
* [Arora et al.2018] Arora, Sanjeev, Rong Ge, Behnam Neyshabur, and Yi Zhang. 2018. "Stronger Generalization Bounds for Deep Nets via a Compression Approach."
* [Bach2017] Bach, Francis. 2017. "Breaking the Curse of Dimensionality with Convex Neural Networks." _Journal of Machine Learning Research_ 18 (19): 1-53.
* [Barron1993] Barron, Andrew R. 1993. "Universal Approximation Bounds for Superpositions of a Sigmoidal Function." _IEEE Transactions on Information Theory_ 39 (3): 930-45.
* [Bartlett1996] Bartlett, Peter L. 1996. "For Valid Generalization, the Size of the Weights Is More Important Than the Size of the Network." In _NIPS_.
* [Bartlett et al.2017] Bartlett, Peter L., Nick Harvey, Chris Liaw, and Abbas Mehrabian. 2017. "Nearly-Tight VC-Dimension and Pseudodimension Bounds for Piecewise Linear Neural Networks."
* [Bartlett and Long2020] Bartlett, Peter L., and Philip M. Long. 2020. "Failures of Model-Dependent Generalization Bounds for Least-Norm Interpolation."
* [Bartlett and Mendelson2002] Bartlett, Peter L., and Shahar Mendelson. 2002. "Rademacher and Gaussian Complexities: Risk Bounds and Structural Results." _JMLR_ 3 (November): 463-82.
* [Bartlett et al.2017] Bartlett, Peter, Dylan Foster, and Matus Telgarsky. 2017. "Spectrally-Normalized Margin Bounds for Neural Networks." _NIPS_.
* [Belkin et al.2018] Belkin, Mikhail, Daniel Hsu, Siyuan Ma, and Soumik Mandal. 2018. "Reconciling Modern Machine Learning Practice and the Bias-Variance Trade-Off."
* [Belkin et al.2019] Belkin, Mikhail, Daniel Hsu, and Ji Xu. 2019. "Two Models of Double Descent for Weak Features."
* [Bengio et al.2011] Bengio, Yoshua, and Olivier Delalleau. 2011. "Shallow Vs. Deep Sum-Product Networks." In _NIPS_.
* [Bietti and Bach2020] Bietti, Alberto, and Francis Bach. 2020. "Deep Equals Shallow for ReLU Networks in Kernel Regimes."
* [Blum and Langford2003] Blum, Avrim, and John Langford. 2003. "PAC-MDL Bounds." In _Learning Theory and Kernel Machines_, 344-57. Springer.
* [Bengio et al.2018]Borwein, Jonathan, and Adrian Lewis. 2000. _Convex Analysis and Nonlinear Optimization_. Springer Publishing Company, Incorporated.
* Bubeck, Sebastien. 2014. "Theory of Convex Optimization for Machine Learning."
* Cao, Yuan, and Gu (2020a) Cao, Yuan, and Quanquan Gu. 2020a. "Generalization Bounds of Stochastic Gradient Descent for Wide and Deep Neural Networks."
* Cao, Yuan, and Gu (2020b) ------. 2020b. "Generalization Error Bounds of Gradient Descent for Learning over-Parameterized Deep ReLU Networks."
* Carmon, Yair, and Duchi (2018) Carmon, Yair, and John C. Duchi. 2018. "Analysis of Krylov Subspace Solutions of Regularized Nonconvex Quadratic Problems." In _NIPS_.
* Chaudhuri, Kamalika, and Dasgupta (2014) Chaudhuri, Kamalika, and Sanjoy Dasgupta. 2014. "Rates of Convergence for Nearest Neighbor Classification."
* Chen, Ricky T. Q., Yulia Rubanova, Jesse Bettencourt, and David Duvenaud. 2018. "Neural Ordinary Differential Equations."
* Chen, Zixiang, Yuan Cao, Quanquan Gu, and Tong Zhang (2020) Chen, Zixiang, Yuan Cao, Quanquan Gu, and Tong Zhang. 2020. "A Generalized Neural Tangent Kernel Analysis for Two-Layer Neural Networks."
* Chen, Zixiang, Yuan Cao, Difan Zou, and Quanquan Gu (2019) Chen, Zixiang, Yuan Cao, Difan Zou, and Quanquan Gu. 2019. "How Much over-Parameterization Is Sufficient to Learn Deep ReLU Networks?"
* Chizat, Lenaic, and Bach (2018) Chizat, Lenaic, and Francis Bach. 2018. "On the Global Convergence of Gradient Descent for Over-parameterized Models using Optimal Transport." _arXiv e-Prints_, May, arXiv:1805.09545. [http://arxiv.org/abs/1805.09545](http://arxiv.org/abs/1805.09545).
* Chizat, Lenaic, and Bach (2019) ------. 2019. "A Note on Lazy Training in Supervised Differentiable Programming."
* Chizat, Lenaic, and Bach (2020) ------. 2020. "Implicit Bias of Gradient Descent for Wide Two-Layer Neural Networks Trained with the Logistic Loss." _arXiv:2002.04486 [math.OC]_.
* Cho, Youngmin, and Saul (2009) Cho, Youngmin, and Lawrence K. Saul. 2009. "Kernel Methods for Deep Learning." In _NIPS_.
* Cisse, Bojanowski, Grave, Dauphin, and Usunier (2017) Cisse, Moustapha, Piotr Bojanowski, Edouard Grave, Yann Dauphin, and Nicolas Usunier. 2017. "Parseval Networks: Improving Robustness to Adversarial Examples."
* Clarke, Francis H., Yuri S. Ledyaev, Ronald J. Stern, and Peter R. Wolenski (1998) Clarke, Francis H., Yuri S. Ledyaev, Ronald J. Stern, and Peter R. Wolenski. 1998. _Nonsmooth Analysis and Control Theory_. Springer.
* Cohen, Nadav, Or Sharir, and Shashua (2016) Cohen, Nadav, Or Sharir, and Amnon Shashua. 2016. "On the Expressive Power of Deep Learning: A Tensor Analysis." In _29th Annual Conference on Learning Theory_, edited by Vitaly Feldman, Alexander Rakhlin, and Ohad Shamir, 49:698-728. Proceedings of Machine Learning Research. Columbia University, New York, New York, USA: PMLR. [http://proceedings.mlr.press/v49/co](http://proceedings.mlr.press/v49/co) hen16.html.
* Cohen, Nadav, and Shashua (2016) Cohen, Nadav, and Amnon Shashua. 2016. "Convolutional Rectifier Networks as Generalized Tensor Decompositions." In _Proceedings of the 33rd International Conference on Machine Learning_, edited by Maria Florina Balcan and Kilian Q. Weinberger, 48:955-63. Proceedings of Machine Learning Research. New York, New York, USA: PMLR. [http://proceedings.mlr.press/v48/cohe](http://proceedings.mlr.press/v48/cohe) nb16.html.
* Cohen, Nadav, and Shashua (2018)Cybenko, George. 1989. "Approximation by superpositions of a sigmoidal function." _Mathematics of Control, Signals and Systems_ 2 (4): 303-14.
* [Daniely, Amit. 2017] Daniely, Amit. 2017. "Depth Separation for Neural Networks." In _COLT_.
* [Daniely, Amit, and Malach. 2020] Daniely, Amit, and Eran Malach. 2020. "Learning Parities with Neural Networks."
* [Davis, Drusvyatskiy, Kakade, and Lee. 2018] Davis, Damek, Dmitriy Drusvyatskiy, Sham Kakade, and Jason D. Lee. 2018. "Stochastic Subgradient Method Converges on Tame Functions."
* [Diakonikolas, Goel, Karmalkar, Klivans, and Soltanolkotabi. 2020] Diakonikolas, Ilias, Surbhi Goel, Sushrut Karmalkar, Adam R. Klivans, and Mahdi Soltanolkotabi. 2020. "Approximation Schemes for ReLU Regression."
* [Du, Wu, Hu, and Lee. 2018] Du, Simon S., Wei Hu, and Jason D. Lee. 2018. "Algorithmic Regularization in Learning Deep Homogeneous Models: Layers Are Automatically Balanced."
* [Du, Zhai, Poczos, and Singh. 2018] Du, Simon S., Xiyu Zhai, Barnabas Poczos, and Aarti Singh. 2018. "Gradient Descent Provably Optimizes over-Parameterized Neural Networks."
* [Du, Zhai, and Zhai. 2018] Du, Simon S, Jason D Lee, Haochuan Li, Liwei Wang, and Xiyu Zhai. 2018. "Gradient Descent Finds Global Minima of Deep Neural Networks." _arXiv Preprint arXiv:1811.03804_.
* [Du, Zhai, and Hu. 2019] Du, Simon, and Wei Hu. 2019. "Width Provably Matters in Optimization for Deep Linear Neural Networks."
* [Dziugaite, Karolina, Drouin, Neal, Rajkumar, Caballero, Wang, Mitliagkas, and Roy. 2020] Dziugaite, Gintare Karolina, and Daniel M. Roy. 2019. "Computing Nonvacuous Generalization Bounds for Deep (stochastic) Neural Networks with Many More Parameters Than Training Data."
* [Eldan, and Shamir. 2015] Eldan, Ronen, and Ohad Shamir. 2015. "The Power of Depth for Feedforward Neural Networks."
* [Folland, 1999] Folland, Gerald B. 1999. _Real Analysis: Modern Techniques and Their Applications_. 2nd ed. Wiley Interscience.
* [Funahashi, Funahashi, and Kawab. 1989] Funahashi, K. 1989. "On the Approximate Realization of Continuous Mappings by Neural Networks." _Neural Netw._ 2 (3): 183-92.
* [Ge, Lee, and Ma. 2016] Ge, Rong, Jason D. Lee, and Tengyu Ma. 2016. "Matrix Completion Has No Spurious Local Minimum." In _NIPS_.
* [Ghorbani, Mei, Misiakiewicz, and Montanari. 2020] Ghorbani, Behrooz, Song Mei, Theodor Misiakiewicz, and Andrea Montanari. 2020. "When Do Neural Networks Outperform Kernel Methods?"
* [Goel, Klivans, Manurangsi, and Reichman. 2020] Goel, Surbhi, Adam Klivans, Pasin Manurangsi, and Daniel Reichman. 2020. "Tight Hardness Results for Training Depth-2 ReLU Networks."
* [Golowich, Rakhlin, and Shamir. 2018] Golowich, Noah, Alexander Rakhlin, and Ohad Shamir. 2018. "Size-Independent Sample Complexity of Neural Networks." In _COLT_.
* [Gunasekar, Lee, Soudry, and Srebro. 2018a] Gunasekar, Suriya, Jason D Lee, Daniel Soudry, and Nati Srebro. 2018a. "Implicit Bias of Gradient Descent on Linear Convolutional Networks." In _Advances in Neural Information Processing Systems_, 9461-71.
* [Gunasekar, Lee, and Srebro. 2018]Gunasekar, Suriya, Jason Lee, Daniel Soudry, and Nathan Srebro. 2018b. "Characterizing Implicit Bias in Terms of Optimization Geometry." _arXiv Preprint arXiv:1802.08246_.
* Gunasekar et al. (2017) Gunasekar, Suriya, Blake Woodworth, Srinadh Bhojanapalli, Behnam Neyshabur, and Nathan Srebro. 2017. "Implicit Regularization in Matrix Factorization."
* Gurvits and Koiran (1995) Gurvits, Leonid, and Pascal Koiran. 1995. "Approximation and Learning of Convex Superpositions." In _Computational Learning Theory_, edited by Paul Vitanyi, 222-36. Springer.
* Hanin and Rolnick (2019) Hanin, Boris, and David Rolnick. 2019. "Deep ReLU Networks Have Surprisingly Few Activation Patterns."
* Hastie et al. (2019) Hastie, Trevor, Andrea Montanari, Saharon Rosset, and Ryan J. Tibshirani. 2019. "Surprises in High-Dimensional Ridgeless Least Squares Interpolation."
* Hertz et al. (1991) Hertz, John, Anders Krogh, and Richard G. Palmer. 1991. _Introduction to the Theory of Neural Computation_. USA: Addison-Wesley Longman Publishing Co., Inc.
* Hiriart-Urruty et al. (2001) Hiriart-Urruty, Jean-Baptiste, and Claude Lemarechal. 2001. _Fundamentals of Convex Analysis_. Springer Publishing Company, Incorporated.
* Hornik et al. (1989) Hornik, K., M. Stinchcombe, and H. White. 1989. "Multilayer Feedforward Networks Are Universal Approximators." _Neural Networks_ 2 (5): 359-66.
* Jacot et al. (2018) Jacot, Arthur, Franck Gabriel, and Clement Hongler. 2018. "Neural Tangent Kernel: Convergence and Generalization in Neural Networks." In _Advances in Neural Information Processing Systems_, 8571-80.
* Ji and Li (2020) Ji, Ziwei. 2020. "Personal Communication."
* Ji et al. (2020) Ji, Ziwei, Miroslav Dudik, Robert E. Schapire, and Matus Telgarsky. 2020. "Gradient Descent Follows the Regularization Path for General Losses." In _COLT_.
* Ji et al. (2021) Ji, Ziwei, Justin D. Li, and Matus Telgarsky. 2021. "Early-Stopped Neural Networks Are Consistent."
* Ji and Telgarsky (2018) Ji, Ziwei, and Matus Telgarsky. 2018. "Gradient Descent Aligns the Layers of Deep Linear Networks." arXiv:1810.02032 [cs.LG].
* Li and Li (2019) ------. 2019a. "Polylogarithmic Width Suffices for Gradient Descent to Achieve Arbitrarily Small Test Error with Shallow ReLU Networks."
* Li and Li (2019) ------. 2019b. "Risk and Parameter Convergence of Logistic Regression." In _COLT_.
* Li and Li (2020) ------. 2020. "Directional Convergence and Alignment in Deep Learning." arXiv:2006.06657 [cs.LG].
* Ji et al. (2020) Ji, Ziwei, Matus Telgarsky, and Ruicheng Xian. 2020. "Neural Tangent Kernels, Transportation Mappings, and Universal Approximation." In _ICLR_.
* Jiang et al. (2020) Jiang, Yiding, Behnam Neyshabur, Hossein Mobahi, Dilip Krishnan, and Samy Bengio. 2020. "Fantastic Generalization Measures and Where to Find Them." In _ICLR_.
* Jin et al. (2017) Jin, Chi, Rong Ge, Praneeth Netrapalli, Sham M. Kakade, and Michael I. Jordan. 2017. "How to Escape Saddle Points Efficiently." In _ICML_.
* Jin et al. (2017)Jones, Lee K. 1992. "A Simple Lemma on Greedy Approximation in Hilbert Space and Convergence Rates for Projection Pursuit Regression and Neural Network Training." _The Annals of Statistics_ 20 (1): 608-13.
* Kakade et al. (2018) Kakade, Sham, and Jason D. Lee. 2018. "Provably Correct Automatic Subdifferentiation for Qualified Programs."
* Kamath et al. (2020) Kamath, Pritish, Omar Montasser, and Nathan Srebro. 2020. "Approximate Is Good Enough: Probabilistic Variants of Dimensional and Margin Complexity."
* Kawaguchi (2016) Kawaguchi, Kenji. 2016. "Deep Learning Without Poor Local Minima." In _NIPS_.
* Kolmogorov and Tikhomirov (1959) Kolmogorov, A. N., and V. M. Tikhomirov. 1959. "\(\epsilon\)-Entropy and \(\epsilon\)-Capacity of Sets in Function Spaces." _Uspekhi Mat. Nauk_ 14 (86, 2): 3-86.
* Ledoux and Talagrand (1991) Ledoux, M., and M. Talagrand. 1991. _Probability in Banach Spaces: Isoperimetry and Processes_. Springer.
* Lee et al. (2017) Lee, Holden, Rong Ge, Tengyu Ma, Andrej Risteski, and Sanjeev Arora. 2017. "On the Ability of Neural Nets to Express Distributions." In _COLT_.
* Lee et al. (2016) Lee, Jason D., Max Simchowitz, Michael I. Jordan, and Benjamin Recht. 2016. "Gradient Descent Only Converges to Minimizers." In _COLT_.
* Leshno et al. (1993) Leshno, Moshe, Vladimir Ya. Lin, Allan Pinkus, and Shimon Schocken. 1993. "Multilayer Feedforward Networks with a Nonpolynomial Activation Function Can Approximate Any Function." _Neural Networks_ 6 (6): 861-67. [http://dblp.uni-trier.de/db/journals/nn/nn6.html#LeshnoLPS93](http://dblp.uni-trier.de/db/journals/nn/nn6.html#LeshnoLPS93).
* Li et al. (2018) Li, Yuanzhi, and Yingyu Liang. 2018. "Learning Overparameterized Neural Networks via Stochastic Gradient Descent on Structured Data."
* Long and Sedghi (2019) Long, Philip M., and Hanie Sedghi. 2019. "Generalization Bounds for Deep Convolutional Neural Networks."
* Luxburg et al. (2004) Luxburg, Ulrike von, and Olivier Bousquet. 2004. "Distance-Based Classification with Lipschitz Functions." _Journal of Machine Learning Research_.
* Lyu and Li (2019) Lyu, Kaifeng, and Jian Li. 2019. "Gradient Descent Maximizes the Margin of Homogeneous Neural Networks."
* Mei et al. (2018) Mei, Song, Andrea Montanari, and Phan-Minh Nguyen. 2018. "A Mean Field View of the Landscape of Two-Layers Neural Networks." _arXiv e-Prints_, April, arXiv:1804.06561. [http://arxiv.org/abs/1804.06561](http://arxiv.org/abs/1804.06561).
* Montanelli et al. (2020) Montanelli, Hadrien, Haizhao Yang, and Qiang Du. 2020. "Deep ReLU Networks Overcome the Curse of Dimensionality for Bandlimited Functions."
* Montufar et al. (2014) Montufar, Guido, Razvan Pascanu, Kyunghyun Cho, and Yoshua Bengio. 2014. "On the Number of Linear Regions of Deep Neural Networks." In _NIPS_.
* Moran and Yehudayoff (2015) Moran, Shay, and Amir Yehudayoff. 2015. "Sample Compression Schemes for VC Classes."
* Nagarajan et al. (2019) Nagarajan, Vaishnavh, and J. Zico Kolter. 2019. "Uniform Convergence May Be Unable to Explain Generalization in Deep Learning."
* Negrea et al. (2019) Negrea, Jeffrey, Gintare Karolina Dziugaite, and Daniel M. Roy. 2019. "In Defense of Uniform Convergence: Generalization via Derandomization with an Application to Interpolating Predictors."Nesterov, Yurii. 2003. _Introductory Lectures on Convex Optimization -- a Basic Course_. Springer.
* [Nesterov, Yurii, and Polyak2006] Nesterov, Yurii, and B. T. Polyak. 2006. "Cubic Regularization of Newton Method and Its Global Performance." _Math. Program._ 108 (1): 177-205.
* [Neyshabur, Bhojanapalli, and Srebro2018] Neyshabur, Behnam, Srinadh Bhojanapalli, and Nathan Srebro. 2018. "A PAC-Bayesian Approach to Spectrally-Normalized Margin Bounds for Neural Networks." In _ICLR_.
* [Neyshabur, Tomioka, and Srebro2014] Neyshabur, Behnam, Ryota Tomioka, and Nathan Srebro. 2014. "In Search of the Real Inductive Bias: On the Role of Implicit Regularization in Deep Learning." _arXiv:1412.6614 [cs.LG]_.
* [Nguyen, Hein.2017] Nguyen, Quynh, and Matthias Hein. 2017. "The Loss Surface of Deep and Wide Neural Networks."
* [Novak, Xiao, Lee, and Shahri2018] Novak, Roman, Lechao Xiao, Jaehoon Lee, Yasaman Bahri, Greg Yang, Jiri Hron, Daniel A. Abolafia, Jeffrey Pennington, and Jascha Sohl-Dickstein. 2018. "Bayesian Deep Convolutional Networks with Many Channels are Gaussian Processes." _arXiv e-Prints_. [http://arxiv.org/abs/1810.05148](http://arxiv.org/abs/1810.05148).
* [Novikoff, Hein.1962] Novikoff, Albert B. J. 1962. "On Convergence Proofs on Perceptrons." _In Proceedings of the Symposium on the Mathematical Theory of Automata_ 12: 615-22.
* [Oymak, Soltanolkotabi.2019] Oymak, Samet, and Mahdi Soltanolkotabi. 2019. "Towards Moderate Overparameterization: Global Convergence Guarantees for Training Shallow Neural Networks." _arXiv Preprint arXiv:1902.04674_.
* [Pisier, Gilles.1980] Pisier, Gilles. 1980. "Remarques Sur Un resultat Non Publie de b. Maurey." _Seminaire Analyse Fonctionnelle (dit)_, 1-12.
* [Rolnick, and Tegmark2017] Rolnick, David, and Max Tegmark. 2017. "The Power of Deeper Networks for Expressing Natural Functions."
* [Safran, Shamir.2016] Safran, Itay, and Ohad Shamir. 2016. "Depth-Width Tradeoffs in Approximating Natural Functions with Neural Networks."
* [Schapire, and Freund2012] Schapire, Robert E., and Yoav Freund. 2012. _Boosting: Foundations and Algorithms_. MIT Press.
* [Schapire, Freund, Bartlett, and Lee1997] Schapire, Robert E., Yoav Freund, Peter Bartlett, and Wee Sun Lee. 1997. "Boosting the Margin: A New Explanation for the Effectiveness of Voting Methods." In _ICML_, 322-30.
* [Schmidt-Hieber, Johannes.2017] Schmidt-Hieber, Johannes. 2017. "Nonparametric Regression Using Deep Neural Networks with ReLU Activation Function."
* [Shallue, Lee, Antognini, Sohl-Dickstein, Frostig, and Dahl2018] Shallue, Christopher J., Jaehoon Lee, Joseph Antognini, Jascha Sohl-Dickstein, Roy Frostig, and George E. Dahl. 2018. "Measuring the Effects of Data Parallelism on Neural Network Training."
* [Shamir, Ohad.2018] Shamir, Ohad. 2018. "Exponential Convergence Time of Gradient Descent for One-Dimensional Deep Linear Neural Networks." _arXiv:1809.08587 [cs.LG]_.
* [Shamir, Ohad, and Zhang2013] Shamir, Ohad, and Tong Zhang. 2013. "Stochastic Gradient Descent for Non-Smooth Optimization: Convergence Results and Optimal Averaging Schemes." In _ICML_.
* [Siegelmann, Sontag.1994] Siegelmann, Hava, and Eduardo Sontag. 1994. "Analog Computation via Neural Networks." _Theoretical Computer Science_ 131 (2): 331-60.
* [Soudry, Hoffer, and Srebro2017] Soudry, Daniel, Elad Hoffer, and Nathan Srebro. 2017. "The Implicit Bias of Gradient Descent on Separable Data." _arXiv Preprint arXiv:1710.10345_.
* [Steinwart, Ingo, and Christmann2008] Steinwart, Ingo, and Andreas Christmann. 2008. _Support Vector Machines_. 1st ed. Springer.
* [Steinwart, Ingo, and Christmann2008]Suzuki, Taiji, Hiroshi Abe, and Tomoaki Nishimura. 2019. "Compression Based Bound for Non-Compressed Network: Unified Generalization Error Analysis of Large Compressible Deep Neural Network."

Telgarsky, Matus. 2013. "Margins, Shrinkage, and Boosting." In _ICML_.

------. 2015. "Representation Benefits of Deep Feedforward Networks."

------. 2016. "Benefits of Depth in Neural Networks." In _COLT_.

------. 2017. "Neural Networks and Rational Functions." In _ICML_.

Tzen, Belinda, and Maxim Raginsky. 2019. "Neural Stochastic Differential Equations: Deep Latent Gaussian Models in the Diffusion Limit."

Vardi, Gal, and Ohad Shamir. 2020. "Neural Networks with Small Weights and Depth-Separation Barriers." _arXiv:2006.00625 [cs.LG]_.

Wainwright, Martin J. 2015. "UC Berkeley Statistics 210B, Lecture Notes: Basic tail and concentration bounds." January 2015. [https://www.stat.berkeley.edu/%C2%A0mjwain/stat210b/](https://www.stat.berkeley.edu/%C2%A0mjwain/stat210b/).

------. 2019. _High-Dimensional Statistics: A Non-Asymptotic Viewpoint_. 1st ed. Cambridge University Press.

Wei, Colin, and Tengyu Ma. 2019. "Data-Dependent Sample Complexity of Deep Neural Networks via Lipschitz Augmentation."

Weierstrass, Karl. 1885. "Uber Die Analytische Darstellbarkeit Sogenannter Willkurlicher Functionen Einer Reellen Veranderlichen." _Sitzungsberichte Der Akademie Zu Berlin_, 633-39, 789-805.

Yarotsky, Dmitry. 2016. "Error Bounds for Approximations with Deep ReLU Networks."

Yehudai, Gilad, and Ohad Shamir. 2019. "On the Power and Limitations of Random Features for Understanding Neural Networks." _arXiv:1904.00687 [cs.LG]_.

------. 2020. "Learning a Single Neuron with Gradient Methods." _arXiv:2001.05205 [cs.LG]_.

Zhang, Chiyuan, Samy Bengio, Moritz Hardt, Benjamin Recht, and Oriol Vinyals. 2017. "Understanding Deep Learning Requires Rethinking Generalization." _ICLR_.

Zhou, Lijia, D. J. Sutherland, and Nathan Srebro. 2020. "On Uniform Convergence and Low-Norm Interpolation Learning."

Zhou, Wenda, Victor Veitch, Morgane Austern, Ryan P. Adams, and Peter Orbanz. 2018. "Non-Vacuous Generalization Bounds at the ImageNet Scale: A PAC-Bayesian Compression Approach."

Zou, Difan, Yuan Cao, Dongruo Zhou, and Quanquan Gu. 2018. "Stochastic Gradient Descent Optimizes over-Parameterized Deep Relu Networks."

Zou, Difan, and Quanquan Gu. 2019. "An Improved Analysis of Training over-Parameterized Deep Neural Networks."