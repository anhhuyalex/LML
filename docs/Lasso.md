\title{
Diagonal Linear Networks and the Lasso Regularization Path
}

\author{
Raphaël Berthier*
}

March 19, 2026

\begin{abstract}
Diagonal linear networks are neural networks with linear activation and diagonal weight matrices. Their theoretical interest is that their implicit regularization can be rigorously analyzed: from a small initialization, the training of diagonal linear networks converges to the linear predictor with minimal 1-norm among minimizers of the training loss. In this paper, we deepen this analysis showing that the full training trajectory of diagonal linear networks is closely related to the lasso regularization path. In this connection, the training time plays the role of an inverse implicit regularization parameter. Both rigorous results and simulations are provided to illustrate this conclusion. Under a monotonicity assumption on the lasso regularization path, the connection is exact while in the general case, we show an approximate connection.
\end{abstract}

\footnotetext{
*Sorbonne Université, Inria, Centre Inria de Sorbonne Université, Paris, France
}

\section*{Contents}
1 Introduction ..... 3
2 The $u \circ v$ case - statement of the results ..... 5
2.1 Connection to the lasso under a monotonicity assumption ..... 6
2.2 Simulations ..... 7
2.3 Approximate connection to the lasso in the general case ..... 7
2.4 Related work and final remarks ..... 9
3 The $u \circ u$ case - statement of the results ..... 10
3.1 Connection to the positive lasso under a monotonicity assumption ..... 11
3.2 Approximate connection to the positive lasso in the general case ..... 11
4 The $u \circ u$ case - proofs of the results ..... 12
4.1 Sketch of proof of Thm. 3.1 ..... 12
4.2 Mirror flow interpretation ..... 15
4.3 Uniform bound on the trajectories ..... 16
4.4 The positive lasso and linear complementarity problems ..... 21
4.5 The positive lasso regularization path and parametric linear com- plementarity problems ..... 22
4.6 Proof of Theorem 3.2 ..... 24
4.7 Proof of Theorem 3.1 ..... 27
5 The $u \circ v$ case - proof of the results ..... 28
5.1 Reductions ..... 28
5.1.1 Reduction of the lasso to the positive lasso ..... 28
5.1.2 Reduction of dynamics in the $u \circ v$ case to the $u \circ u$ case ..... 30
5.2 Proofs ..... 31
5.2.1 Proof of Theorem 2.1 ..... 31
5.2.2 Proof of Theorem 2.2 ..... 32
References ..... 32

\section*{1 Introduction}

Context. The composition of layers enables a neural network to learn a modular representation of the data. However, the reasons why learning the components of this representation is computationally amenable through gradient descent methods and why it leads to excellent generalization properties are still not fully understood [3].

In order to address this question, machine learning theory has studied the gradient flow training of linear networks-where the activation is linear-and diagonal linear networks (DLNs)-where, in addition, weight matrices are diagonal. We now provide a brief mathematical introduction to DLNs (see references below for more details).

Consider the minimization of quadratic function:
$$
\ell(x)=\frac{1}{2}\langle x, M x\rangle-\langle r, x\rangle, \quad x \in \mathbb{R}^{d} .
$$
We assume that this function is convex, i.e. that $M$ is positive semidefinite, and that it is lower-bounded, i.e. that $r \in \operatorname{Span} M$. The minimization of such functions arises, e.g., when solving linear least-squares problems.

A DLN (with two layers) consists in parametrizing $x=u \circ v$, where ∘ denotes the component-wise product of the two vectors $u, v \in \mathbb{R}^{d}$. We then train the weights $u, v$ by the gradient flow on the loss $\ell(u \circ v)$, potentially regularizing by the 2-norm of $u, v$ (weight decay):
$$
\begin{align*}
& L(u, v)=\ell(u \circ v)+\frac{\lambda}{2}\left(\|u\|^{2}+\|v\|^{2}\right), \quad \lambda \geqslant 0,  \tag{1.1}\\
& \frac{\mathrm{~d} u}{\mathrm{~d} t}=-\nabla_{u} L(u, v), \quad \frac{\mathrm{d} v}{\mathrm{~d} t}=-\nabla_{v} L(u, v) . \tag{1.2}
\end{align*}
$$
This induces a trajectory for the weights $u(t), v(t)$ as well as an effective linear parameter $x(t)=u(t) \circ v(t)$.

A first observation is that, under mild assumptions, $x(t)$ converges to a minimizer of the lasso problem
$$
\min _{\cdot x \in \mathbb{R}^{d}}\left\{\ell(x)+\lambda\|x\|_{1}\right\} .
$$
See, e.g., [31]. However, a stronger intriguing phenomenon was observed without weight decay $(\lambda=0)$ : when initialized from a suitable infinitesimal initialization $x(0)$, the training of DLNs is shown to converge to the minimizer of $\ell$ with mininimal 1-norm [34]. As a consequence, the minimizer selected by the training of a DLN benefits from a sparsifying effect, even without any explicit regularization present in the loss function $L$. This phenomenon, called implicit regularization, is beneficial for the generalization properties of the trained network. Implicit regularization has been observed in other neural network structures and suggested to be a key ingredient in the success of neural networks [32]. See, e.g., [15, 21, 8, 20] for contributions to the implicit regularization of neural networks and [33, 35, 34, 16, 20, 2, 27, 28, 25, 9, 4, 26] for more contributions specifically on DLNs.

Contributions. In this article, we show that DLNs enjoy a stronger implicit regularization when early stopped, and connect the training trajectory of DLNs to the lasso regularization path.

For a parameter $\mu \geqslant 0$, we define the lasso objective as
$$
\begin{equation*}
\operatorname{Lasso}(x, \mu)=\ell(x)+\left(\lambda+\frac{1}{\mu}\right)\|x\|_{1} . \tag{1.3}
\end{equation*}
$$
This non-standard parametrization of the lasso regularization is convenient to separate the explicit regularization $\lambda\|x\|_{1}$ (that stems from weight decay) from the implicit regularization $\frac{1}{\mu}\|x\|_{1}$. The results below will clarify why it is convenient to parametrize the implicit regularization by its inverse regularization parameter $\mu$. In all of this paper, the reader can choose to consider the case $\lambda=0$ for simplicity, as it is the most relevant case for the study of implicit regularization.

The connection between the training trajectory and the lasso regularization path holds in the same infinitesimal initialization limit as the convergence to the minimum 1-norm solution described above. When $x(0)$ is of magnitude $\varepsilon \ll 1$, the time $t$ is jointly rescaled as $t(s, \varepsilon)=\frac{1}{2}\left(\log \frac{1}{\varepsilon}\right) s$. Consider the average of the trajectory of $x$ :
$$
\bar{x}(t)=\frac{1}{t} \int_{0}^{t} x(u) \mathrm{d} u .
$$
We then have the following informal result: for all $s>0$, as $\varepsilon \rightarrow 0, \bar{x}(t(s, \varepsilon))$ (approximately) minimizes the lasso objective Lasso $(., s)$.

In the informal result above, the parenthesized word "approximately" refers to a more technical discussion. Under a certain monotonicity assumption on the lasso regularization path, we show that Lasso $(\bar{x}(t(s, \varepsilon)), s)$ converges to the minimum of $\operatorname{Lasso}(., s)$ as $\varepsilon \rightarrow 0$. However, when the lasso regularization path is not monotone, we only show that $\bar{x}(t(s, \varepsilon))$ is an approximate minimizer of Lasso $(., s)$, even in the limit $\varepsilon \rightarrow 0$, where the suboptimality gap is controled by the deviation from the monotonicity assumption. This distinction is also apparent in simulations.

Overall, this result shows that early stopping the training of DLNs can offer a tradeoff between sparsity and data fitting. An earlier stopping time leads to a sparser linear model. This deepens the connection between DLNs and sparse regression.

Our results also cover the case $x=u \circ u$, that is less motivated by the theoretical study of neural networks, but that is algebraically more elegant. As a consequence, we provide the proofs in the $u \circ u$ case first, and then deduce the proofs in the $u \circ v$ by a reduction to the $u \circ u$ case. This systematic reduction strategy might be of independent interest for the study of DLNs.

Outline. Sec. 2 is the one of interest for most readers. It contains the results in the case $x=u \circ v$ and their discussions. Sec. 2.1 provides the exact connection under the monotonicity assumption on the lasso regularization path; Sec. 2.2 presents simulations that illustrate the results; and Sec. 2.3 covers the general
case, beyond the monotonicity assumption. Sec. 2.4 concludes this section by discussing in more detail the related work and a speculative conclusion for the theory of neural networks.

Sec. 3 contains the parallel results in the case $x=u \circ u$. Sec. 4 contains the proofs of the results in the $u \circ u$ case. This section contains the bulk of the technical effort of this paper, as the proofs in the $u \circ v$ case, provided in Sec. 5, are obtained by a systematic reduction to the $u \circ u$ case.

Notations. We denote $\langle.,$.$\rangle the canonical inner product on \mathbb{R}^{d}$ and $\|$.$\| the$ associated norm. We note $\|.\|_{1}$ the 1-norm on vectors: $\|x\|_{1}=\sum_{i=1}^{d}\left|x_{i}\right|$.

We use the notation $x \geqslant 0$ to denote that $x$ has all coordinates nonnegative. If $x$ is a real number, we denote $x_{+}=\max (x, 0)$ its positive part and $x_{-}=$ $\max (-x, 0)$ its negative part.

When $\varphi: \mathbb{R} \rightarrow \mathbb{R}$ and $x \in \mathbb{R}^{d}$, we denote $\varphi(x)=\left(\varphi\left(x_{1}\right), \ldots, \varphi\left(x_{d}\right)\right)$ the component-wise application of $\varphi$ to $x$. This notation is used, for instance, for $\varphi=\log$, for $\varphi(x)=x^{2}$, for $\varphi(x)=x_{+}$or for $\varphi(x)=x_{-}$. We thus denote $x^{2}=x \circ x$.

We sometimes write explicitly the dependence of some positive constants on some parameters, for instance $C_{i}=C_{i}(M, r, \alpha)$. Without any index, the notation $C(\ldots)$ indicates a positive constant that depends on the parameters between the parentheses. This constant can change from one occurrence to the next.

We denote $\mathbb{1}=(1, \ldots, 1)$ the vector of ones, whose dimension is implicit from the context.

When $I$ is a subset of $\{1, \ldots, d\}$, we denote $A_{I}$ the submatrix of $A$ where the columns whose index are in $I$ are selected, and $A_{I, I}$ the submatrix of $A$ where both the rows and the columns whose index are in $I$ are selected.

When $f$ is a function of $z$, we denote $\min _{.} f(z)$ the minimization problem of $f$, and $\min _{z} f(z)$ its minimal value. In other words, min. stands for "minimize" and min stands for "minimum".

\section*{2 The $u \circ v$ case - statement of the results}

Setting. We study the solution of Eqs. (1.1), (1.2) in the limit of small initialization. More precisely, we denote $u^{\varepsilon}(t)$ and $v^{\varepsilon}(t)$ the solutions of Eqs. (1.2) with initial conditions $u^{\varepsilon}(0)=\sqrt{\varepsilon} \beta$ and $v^{\varepsilon}(0)=\sqrt{\varepsilon} \gamma$, where $\beta$ and $\gamma$ are fixed vectors in $\mathbb{R}^{d}$ and $\varepsilon$ is a small parameter. We denote $x^{\varepsilon}(t)=u^{\varepsilon}(t) \circ v^{\varepsilon}(t)$. The scalings in $\varepsilon$ are chosen so that $x^{\varepsilon}(0)$ is of order $\varepsilon$. For non-degeneracy reasons, we assume that for all $i \in\{1, \ldots, d\}, \beta_{i} \neq \pm \gamma_{i}$.

We also define $\bar{x}^{\varepsilon}(t)=\frac{1}{t} \int_{0}^{t} x^{\varepsilon}(u) \mathrm{d} u$ the average of the trajectory of $x^{\varepsilon}$. The goal of our analyses is to connect the average of the trajectory to the lasso optimization problem
$$
\begin{equation*}
\min _{\cdot x \in \mathbb{R}^{d}} \operatorname{Lasso}(x, \mu) . \tag{2.1}
\end{equation*}
$$

We denote $\operatorname{Lasso}_{*}(\mu)=\min _{x \in \mathbb{R}^{d}} \operatorname{Lasso}(x, \mu)$ the minimum of this optimization problem.

Define a rescaled time
$$
\begin{equation*}
s=\frac{2}{\log \frac{1}{\varepsilon}} t \tag{2.2}
\end{equation*}
$$

Below, we frequently abuse notations and use the same notation for rescaled functions of time. For instance, $\bar{x}^{\varepsilon}(s)$ denotes $\bar{x}^{\varepsilon}(t)$ where $t=t(\varepsilon)=\frac{s}{2} \log \frac{1}{\varepsilon}$.

\subsection*{2.1 Connection to the lasso under a monotonicity assumption}

Theorem 2.1. For all $\mu>0$, let $x(\mu)$ denote a minimizer of the lasso
$$
\min _{x \in \mathbb{R}^{d}} \operatorname{Lasso}(x, \mu) .
$$
Assume that $\mu>0 \mapsto \mu x(\mu)$ is coordinate-wise monotone. Then, for all $s>0$,
$$
\operatorname{Lasso}\left(\bar{x}^{\varepsilon}(s), s\right) \underset{\varepsilon \rightarrow 0}{\longrightarrow} \operatorname{Lasso}_{*}(s) .
$$

We insist that in the above result, the rescaled time $s=\frac{2}{\log 1 / \varepsilon} t$ is kept fixed and $t=t(\varepsilon)=\frac{s}{2} \log \frac{1}{\varepsilon}$ diverges as $\varepsilon \rightarrow 0$. This is necessary to obtain a non-trivial limit for $\bar{x}^{\varepsilon}$.

This result identifies the rescaled time $s$ with the inverse implicit regularization parameter $\mu$ of the lasso. In the limit $\varepsilon \rightarrow 0$, a single training trajectory of the DLN computes the full lasso regularization path. Different stopping times correspond to different regularization levels; the earlier the stopping, the more regularized the solution.

For instance, for $s$ small enough, the regularization level is large enough so that the unique lasso minimizer is $0 \in \mathbb{R}^{d}$. This is consistent with the fact that the DLN dynamics (1.2) are initialized $\sqrt{\varepsilon}$-close to the fixed point $(u, v)=(0,0)$, thus they will escape this fixed point in a time proportional to $\log \frac{1}{\varepsilon}$. As a consequence, for $s$ small enough, $x=u \circ v$ is at 0 (in the limit $\varepsilon \rightarrow 0$ ).

Further, as $s \rightarrow \infty$, we obtain that the regularization level is infinitesimal. In the case $\lambda=0$ (no weight decay), this is consistent with the fact that the DLN dynamics converge to a minimizer of $\ell$ with minimal 1-norm [34].

However, Thm. 2.1 provides an interpolation between these two asymptotics. For finite $s, \bar{x}^{\varepsilon}(s)$ minimizes $\operatorname{Lasso}(., s)$ in the limit $\varepsilon \rightarrow 0$.

We insist on the fact that $\operatorname{Lasso}(., s)$ does not have a unique minimizer a priori, thus one can not define the lasso minimizer or the lasso regularization path. Our claim is that, if there is $a$ lasso regularization path $x(\mu)$ such that $\mu \mapsto \mu x(\mu)$ is monotone, then $\bar{x}^{\varepsilon}(s)$ minimizes $\operatorname{Lasso}(., s)$ in the limit $\varepsilon \rightarrow$ 0 . In particular, we do not claim that $\bar{x}^{\varepsilon}(s) \xrightarrow[\varepsilon \rightarrow 0]{ } x(s)$. To the best of our understanding, the limit of $\bar{x}^{\varepsilon}(s)$ depends more subtely on the initialization vectors $\beta$ and $\gamma$; this will not be discussed further in this paper.

A sufficient condition for $\mu \mapsto \mu x(\mu)$ to be monotone is to have the lasso regularization path $\mu \mapsto x(\mu)$ itself monotone (as $\lim _{\mu \rightarrow 0^{+}} x(\mu)=0$ ). Under the latter condition, the lasso regularization path has already been shown to be equivalent to computationally cheaper algorithms such as the least angle regression algorithm [14], incremental forward stagewise regression [17] or boosting [29]. Moreover, it is also argued that even when $\mu \mapsto x(\mu)$ is not monotone, the solutions of these different algorithms might not be very far, see for example Figure 1 in [14]. A sufficient condition for the lasso regularization path to be monotone, derived in the latter article, is to have $S\left(M_{I I}\right)^{-1} S \mathbb{1} \geqslant 0$ for all subsets $I \subset\{1, \ldots, d\}$ and for all diagonal sign matrices $S \in \mathbb{R}^{|I| \times|I|}$ (see also [17], Sec. 6, for a succinct statement).

The monotonicity of $\mu \mapsto \mu x(\mu)$ specifically has been studied, to the best of our knowledge, only in the case of the positive lasso, which corresponds to the parametrization $x=u^{2}$, see Sec. 3.1.

\subsection*{2.2 Simulations}

In order to illustrate the results of this paper and discuss the importance of the monotonicity assumption, we provide some simulations. The code is available on github [5].

We randomly generate problem instances in dimension $d=4$ as follows. We consider the quadratic function $\ell(x)=\frac{1}{2}\|X x-y\|^{2}$, where $n=3, X \in \mathbb{R}^{n \times d}$ and $y \in \mathbb{R}^{n}$ are independent and have i.i.d. standard normal entries. We do not put any explicit regularization: $\lambda=0$.

In this case, the lasso regularization path is almost surely unique [30]. We observe empirically that $\mu \mapsto \mu x(\mu)$ is monotone with probability 0.76 , over 1000 random instances. Thus Theorem 2.1 applies in a majority of cases.

In all simulations, we take $\varepsilon=10^{-5}, \beta=\mathbb{1}$ and $\gamma=0$.
Figure 1 compares the average trajectory $\bar{x}^{\varepsilon}(s)$ of DLNs with the lasso regularization path $x(\mu)$ on problems generated randomly as above. When identifying $s=\mu$, the trajectory $\bar{x}^{\varepsilon}(s)$ is qualitatively similar to $x(s)$ in all instances, and the suboptimality gap (Lasso $\left(\bar{x}^{\varepsilon}(s), s\right)$ - $\operatorname{Lasso}_{*}(s)$ )/ $\operatorname{Lasso}_{*}(s)$ remains relatively small (below 0.04 on the provided instances). However, the comparison is much tighter in the monotone case than in the nonmonotone case; in particular, the suboptimality gap is an order of magnitude smaller for monotone instances.

\subsection*{2.3 Approximate connection to the lasso in the general case}

We now provide an approximate optimality result in the nonmonotone case that comforts the simulations.

Theorem 2.2. For all $\mu>0$, let $x(\mu)$ denote a minimizer of the lasso
$$
\min _{x \in \mathbb{R}^{d}} \operatorname{Lasso}(x, \mu) .
$$

\begin{figure}
\includegraphics[alt={},max width=\textwidth]{https://cdn.mathpix.com/cropped/122503bd-387e-42f6-90ed-54d3ca7aaf42-08.jpg?height=1484&width=1201&top_left_y=462&top_left_x=459}
\captionsetup{labelformat=empty}
\caption{Figure 1: Comparison between the average trajectory $\bar{x}^{\varepsilon}(s)$ of DLNs and the lasso regularization path $x(\mu)$. In the subfigure (a), problems instances are generated randomly conditionally on the monotonicity of $\mu \mapsto \mu x(\mu)$. Conversely, in the subfigure (b), problems instances are generated randomly conditionally on the non-monotonicity of $\mu \mapsto \mu x(\mu)$. We provide two instances of each case, one in each column. In each instance, we plot the coordinates $\bar{x}_{i}^{\varepsilon}(s)$ along with $x_{i}(\mu)$, and the suboptimality gap (Lasso $\left(\bar{x}^{\varepsilon}(s), s\right)$ - $\operatorname{Lasso}_{*}(s)$ )/ $\operatorname{Lasso}_{*}(s)$. Simulation details are provided in Sec. 2.2.}
\end{figure}

Assume that $\mu>0 \mapsto x(\mu)$ is absolutely continuous on compact subsets of $(0,+\infty)$. Define $z(\mu)=\mu x(\mu)$ and
$$
\begin{equation*}
z^{\downarrow}(\mu)=\sum_{i=1}^{d} \int_{0}^{\mu}(1+u)\left[\left(\frac{\mathrm{d}\left(z_{i}(u)_{+}\right)}{\mathrm{d} u}\right)_{-}+\left(\frac{\mathrm{d}\left(z_{i}(u)_{-}\right)}{\mathrm{d} u}\right)_{-}\right] \mathrm{d} u . \tag{2.3}
\end{equation*}
$$
Heuristically, $z^{\downarrow}(\mu)$ quantifies the deviation from monotonicity of $z(\mu)$.
Then, there exists a constant $C=C(d, M, r, \lambda, \beta, \gamma)>0$ such that, for all $s>0$,
$$
\begin{align*}
& \limsup _{\varepsilon \rightarrow 0} \operatorname{Lasso}\left(\bar{x}^{\varepsilon}(s), s\right) \leqslant \operatorname{Lasso}_{*}(s)+C \eta\left(\lambda, s, z^{\downarrow}(s)\right), \\
& \text { where } \eta\left(\lambda, s, z^{\downarrow}\right)=(1+\lambda s)\left[\frac{\left(z^{\downarrow}\right)^{1 / 2}}{s}+\frac{z^{\downarrow}}{s^{2}}\right] . \tag{2.4}
\end{align*}
$$

Note that $\eta(\lambda, s, 0)=0$; this enables to derive Thm. 2.1 from Thm. 2.2. The above theorem predicts that the suboptimality gap spikes when the lasso regularization path is not monotone (when $z^{\downarrow}(s)$ is large) and then decays afterwards (as $s$ increases). This is consistent with the observations in Figure 1.

\subsection*{2.4 Related work and final remarks}

Additional related work. In contrast with many works on diagonal linear networks, this paper does not assume any statistical model for the data that generated the loss $\ell$, and focuses only on the optimization analysis. In particular, our results could cover noisy or noiseless data, and general design matrices. This is in contrast with many works that require a restricted isometry property, or a coherence assumption on the design matrix [33, 35, 20].

Under a statistical linear model with additive noise, early stopping is used in DLNs without weight decay to achieve optimal rates [33, 35, 20]. Similarly, in the same setting, the regularization parameter of the lasso is usually chosen proportional to the magnitude of the additive noise, see [18], Chapter 11. Our work sheds light on this correspondence: a non-zero regularization parameter corresponds to a finite stopping time.

More specifically, some earlier works have noted the similarity between the trajectory of DLNs and the lasso regularization path [33, 4, 26]. Vaskevicius et al. noted that $t / \log \frac{1}{\varepsilon}$ plays the role of an inverse regularization parameter in their statistical guarantee [33] (see discussion below their Thm. 1). However, they note that "the gradient descent optimization path [of DLNs] [...] exhibits qualitative and quantitative differences from the lasso regularization path." Our contribution argues that the qualitative differences are actually due to the fact that the lasso regularization path corresponds to the averaged gradient descent optimization path. Finally, the author proved Thm. 3.1, the equivalent of Thm. 2.1 in the case $x=u \circ u$, but only when $M$ is a matrix with non-positive off-diagonal entries [4]. (In this case, the monotonicity assumption is guaranteed.)

Final remarks. This work strengthens our understanding of the implicit regularization of neural networks. Not only the asymptotic convergence point is implicitely regularized, but also the full trajectory of the neural network. The earlier the neural network is stopped, the more regularized the solution is.

Our proof technique provides a way to analyze the implicit regularization in a dynamical way, that is, as time evolves. We hope that this new perspective will help to tackle a major difficulty of the implicit regularization line of research: we do not know how to describe the implicit regularization of more complex neural networks, beyond DLNs. For instance, the implicit regularization of matrix factorization problems can not be described by the nuclear norm, as one would expect from a natural generalization of the results on DLNs [1, 22]. We hope that this discrepancy can be understood through a dynamical study of the deviation between matrix factorization dynamics and nuclear norm minimizers.

\section*{3 The $u \circ u$ case - statement of the results}

Setting. In this section, we state an alternative version of the results of this paper, in the case where the regressor $x$ is parametrized as $x=u^{2}=u \circ u$ instead of $x=u \circ v$. It could be seen as a weight-tied version of DLNs where we impose the same weights in the two layers: $u=v$. Actually, this weight-tied model of neural networks is not of direct interest, and it has the advantage of constraining the sign of $x$. However, it enables a more elegant theory. Moreover, as we discuss in Section 5, the case $x=u \circ v$ can be reduced to the case $x=u^{2}$, thus in fact the bulk of the theory is contained in this case, and the case $x=u \circ v$ follows as corollaries.

Taking $u=v$ in Eqs. (1.1), (1.2), we obtain the dynamics in the $x=u \circ u$ case:
$$
\begin{align*}
& L(u)=\ell\left(u^{2}\right)+\lambda\|u\|^{2}, \quad \lambda \geqslant 0,  \tag{3.1}\\
& \frac{\mathrm{~d} u}{\mathrm{~d} t}=-\nabla_{u} L(u) . \tag{3.2}
\end{align*}
$$
In this case, the gradient flow dynamics can be written a closed-form differential equation in $x=u^{2}$ :
$$
\begin{equation*}
\frac{\mathrm{d} x}{\mathrm{~d} t}=-4 x \circ \nabla \ell(x)-4 \lambda x \tag{3.3}
\end{equation*}
$$
In this section, we denote $u^{\varepsilon}(t)$ the solution of Eq. (3.2) with initial condition $u^{\varepsilon}(0)=\sqrt{\varepsilon} \alpha$ where $\alpha$ is a fixed vector in $\mathbb{R}^{d}$ and $\varepsilon$ is a small parameter. We denote $x^{\varepsilon}(t)=u^{\varepsilon}(t)^{2}$. We assume that all coordinates $\alpha_{i}$ of $\alpha$ are nonzero: if $\alpha_{i}=0$, by Eq. (3.3), the coordinate of $x_{i}^{\varepsilon}(t)$ remains zero for all $t \geqslant 0$, thus this case is degenerate.

Again, we define $\bar{x}^{\varepsilon}(t)=\frac{1}{t} \int_{0}^{t} x^{\varepsilon}(u) \mathrm{d} u$ the average of the trajectory of $x$. The goal of our analyses is to connect the average of the trajectory to the positive lasso optimization problem
$$
\begin{equation*}
\min _{x \geqslant 0} . \operatorname{Lasso}(x, \mu), \tag{3.4}
\end{equation*}
$$
where the lasso objective is defined in Eq. (1.3).
We denote $\operatorname{PosLasso}_{*}(\mu)=\min _{x \geqslant 0} \operatorname{Lasso}(x, \mu)$ the minimum of this optimization problem.

Define a rescaled time
$$
\begin{equation*}
s=\frac{4}{\log \frac{1}{\varepsilon}} t \tag{3.5}
\end{equation*}
$$

\subsection*{3.1 Connection to the positive lasso under a monotonicity assumption}

Theorem 3.1. For all $\mu>0$, let $x(\mu)$ denote a minimizer of the positive lasso
$$
\min _{x \geqslant 0} . \operatorname{Lasso}(x, \mu) .
$$
Assume that $\mu>0 \mapsto \mu x(\mu)$ is coordinate-wise nondecreasing. Then, for all $s>0$,
$$
\operatorname{Lasso}\left(\bar{x}^{\varepsilon}(s), s\right) \underset{\varepsilon \rightarrow 0}{\longrightarrow} \operatorname{PosLasso}_{*}(s) .
$$

The monotonicity of $\mu \mapsto \mu x(\mu)$ translates into the monotonicity of the solution of the parametric linear complementarity problem (4.11), introduced in Sec. 4.5. This monotonicity has first been studied in a different context, the analysis of elastoplastic structures [11]. Cottle proposed an algorithm to test whether the solution of a given problem is monotone, and derived necessary and sufficient conditions under which monotonicity holds for all possible values of $r$ [10]. See also [24] when $M$ is non-invertible. A sufficient condition for monotonicity is when $M$ is a positive definite matrix with non-positive offdiagonal entries. The author has proved Thm. 3.1 under this more restrictive assumption [4].

\subsection*{3.2 Approximate connection to the positive lasso in the general case}

We now turn to the general case.
Theorem 3.2. For all $\mu>0$, let $x(\mu)$ denote a minimizer of the positive lasso
$$
\min _{x \geqslant 0} . \operatorname{Lasso}(x, \mu) .
$$
Assume that $\mu>0 \mapsto x(\mu)$ is absolutely continuous on compact subsets of $(0,+\infty)$. Define $z(\mu)=\mu x(\mu)$ and
$$
\begin{equation*}
z^{\downarrow}(\mu)=\sum_{i=1}^{d} \int_{0}^{\mu}(1+u)\left(\frac{\mathrm{d} z_{i}(u)}{\mathrm{d} u}\right)_{-} \mathrm{d} u . \tag{3.6}
\end{equation*}
$$
Heuristically, $z^{\downarrow}(\mu)$ quantifies the deviation from monotonicity of $z(\mu)$.

Then, there exists a constant $C=C(d, M, r, \lambda, \alpha)>0$ such that, for all $s>0$,
$$
\limsup _{\varepsilon \rightarrow 0} \operatorname{Lasso}\left(\bar{x}^{\varepsilon}(s), s\right) \leqslant \operatorname{PosLasso}_{*}(s)+C \eta\left(\lambda, s, z^{\downarrow}(s)\right),
$$
where $\eta\left(\lambda, s, z^{\downarrow}\right)$ is defined in Eq. (2.4).

\section*{4 The $u \circ u$ case - proofs of the results}

This section is organized as follows. In Sec. 4.1, we provide a sketch of the proof of Thm. 3.1. The following four subsections gather some elements to prepare the detailed proofs. In Sec. 4.2, we recall the mirror flow perspective on the DLN dynamics [23]. In Sec. 4.3, we prove a preliminary bound on the DLN dynamics, that is uniform in time $t$ and for $\varepsilon$ small enough. Its proof is independent from the rest of the proofs, and can be skipped in a first reading. Sec. 4.4 introduces linear complementary problems. Sec. 4.5 extends this introduction to parametric linear complementarity problems, where a parameter $\mu$ varies in the problem. Finally, in Sec. 4.6, we prove Thm. 3.2 and in Sec. 4.7, we deduce the proof of Thm. 3.1.

Additional notations for the proofs. When applied to a $d \times d$ matrix, $\|$. denotes the operator norm associated to the norm $\|$.$\| on \mathbb{R}^{d}$. When $A$ is a positive semidefinite matrix, we denote $\langle., .\rangle_{A}=\langle., A$.$\rangle the semidefinite inner$ product associated to $A$ and $\|.\|_{A}$ the associated seminorm.

When $A \in \mathbb{R}^{d \times k}$ is a matrix, we denote $A^{\dagger} \in \mathbb{R}^{k \times d}$ its Moore-Penrose pseudo-inverse.

If $f: \mathbb{R}^{d} \rightarrow \mathbb{R}$ is a function that has a unique minimizer on a set $C$, then we denote $\operatorname{argmin}_{x \in C} f(x)$ this unique minimizer.

\subsection*{4.1 Sketch of proof of Thm. 3.1}

In this section, we give the main intuitions of the proof. The detailed proof provided in the next sections does not follow exactly this sketch for technical reasons, but we still hope that this section will help the reader to interpret the detailed proof.

On a conceptual level, Thm. 3.1 draws a connection between the positive lasso regularization path and the DLN dynamics. The relationship between both objects is far from obvious. We propose to understand the connection through two intermediate objects: parametric linear complementarity problems (LCPs) and LCPs with derivatives. The structure of connections is summarized below.
![](https://cdn.mathpix.com/cropped/122503bd-387e-42f6-90ed-54d3ca7aaf42-13.jpg?height=471&width=1061&top_left_y=434&top_left_x=523)

In this diagram, vertical arrows are connections provided by duality, in a sense that we make precise below. Once these dual perspectives are established, the positive lasso regularization path and the DLN dynamics are transformed into a parametric LCP and a LCP with derivatives, respectively. Their connection is then much easier to grasp, as suggested by the similarity in the names and in the mathematical formulations. Note that a matching between the parametric LCP and the LCP with derivatives requires to identify $s=\mu$, i.e., the rescaled time $s$ corresponds to an inverse regularization parameter $\mu$.

We now provide more details on each of these connections.

The lasso regularization path and the parametric LCP. The LCP corresponds to the primal-dual formulation of the positive lasso, where $z$ is the primal variable and $w$ the dual variable. As $\operatorname{Lasso}(., \mu)$ is a convex quadratic function on the constraint set $\{x \geqslant 0\}$, the stationarity condition writes as a linear equation, and is combined with primal feasibility $z \geqslant 0$, dual feasibility $w \geqslant 0$ and complementary slackness $\langle w, z\rangle=0$. The lasso regularization path corresponds to the parametrization of this LCP as a function of $\mu$, hence the name parametric LCP. This connection is detailed in Secs. 4.4-4.5.

The DLN dynamics and the LCP with derivatives. The DLN dynamics can also be given a primal-dual interpretation, through their mirror flow interpretation (see Sec. 4.2): the DLN dynamics (3.3) can be written as a mirror flow
$$
\frac{\mathrm{d} \nabla h(x)}{\mathrm{d} t}=-\nabla \widetilde{L}(x), \quad \text { where } \widetilde{L}(x)=\ell(x)+\lambda\langle\mathbb{1}, x\rangle .
$$
where $h(x)=\frac{1}{4} \sum_{i=1}^{d}\left(x_{i} \log x_{i}-x_{i}\right)$ is the entropy potential function; $\nabla h(x)=$ $\frac{1}{4} \log x$ is the dual variable. For scaling reasons as $\varepsilon \rightarrow 0$, we will actually consider a rescaled dual variable
$$
w^{\varepsilon}(s)=-\frac{4}{\log \frac{1}{\varepsilon}} \nabla h\left(x^{\varepsilon}(s)\right)=-\frac{1}{\log \frac{1}{\varepsilon}} \log x^{\varepsilon}(s) .
$$

This rescaled version particularly fits the analysis in the rescaled time $s$. For instance,
$$
\frac{\mathrm{d} w^{\varepsilon}}{\mathrm{d} s}=-\frac{4}{\log \frac{1}{\varepsilon}} \frac{\mathrm{~d} t}{\mathrm{~d} s} \frac{\mathrm{~d} \nabla h\left(x^{\varepsilon}\right)}{\mathrm{d} t}=\nabla \widetilde{L}\left(x^{\varepsilon}\right)=M x^{\varepsilon}-r+\lambda \mathbb{1} .
$$
One can also write $x_{i}^{\varepsilon}(s)=\varepsilon^{w_{i}^{\varepsilon}(s)}$. In other words, the dual variable $w^{\varepsilon}(s)$ encodes the scale of $x^{\varepsilon}(s)$ in $\varepsilon$. At initialization, $x^{\varepsilon}$ is of order $\varepsilon$, thus $w^{\varepsilon}(0) \approx \mathbb{1}$. (We use approximate symbols to denote relations that are rigorous in a certain sense when $\varepsilon \rightarrow 0$.) As the trajectories of $x^{\varepsilon}(s)$ are uniformly bounded (see Sec. 4.3), we must have $w^{\varepsilon}(s) \gtrsim 0$. Finally, when $w_{i}^{\varepsilon}(s)$ is positive, $x_{i}^{\varepsilon}(s)$ converges to 0 as $\varepsilon \rightarrow 0$, thus we have the (approximate) complementary slackness $\left\langle w^{\varepsilon}(s), x^{\varepsilon}(s)\right\rangle \approx 0$.

We thus have the system
$$
\begin{aligned}
& \frac{\mathrm{d} w^{\varepsilon}}{\mathrm{d} s}=M x^{\varepsilon}-r+\lambda \mathbb{1}, \\
& w^{\varepsilon} \gtrsim 0, \quad x^{\varepsilon} \geqslant 0, \quad\left\langle w^{\varepsilon}, x^{\varepsilon}\right\rangle \approx 0 .
\end{aligned}
$$
Writing $z^{\varepsilon}(s)=\int_{0}^{s} x^{\varepsilon}(u) \mathrm{d} u$ and integrating the first equation, this gives the so-called LCP with derivatives [19]
$$
\begin{aligned}
& w^{\varepsilon}=M z^{\varepsilon}-s r+(1+\lambda s) \mathbb{1} \\
& w^{\varepsilon} \gtrsim 0, \quad \frac{\mathrm{~d} z^{\varepsilon}}{\mathrm{d} s} \geqslant 0, \quad\left\langle w^{\varepsilon}, \frac{\mathrm{d} z^{\varepsilon}}{\mathrm{d} s}\right\rangle \approx 0 .
\end{aligned}
$$

The parametric LCP and the LCP with derivatives. We now identify $s=\mu$ to help a correspondence. If the solution of the parametric LCP is assumed to be monotone in its parameter, then it is also a solution of the LCP with derivatives [19]. The monotonicity assumption of Thm. 3.1 corresponds to this requirement.

Finally, if $M$ is positive definite, the solution of the LCP with derivatives is unique (up to initialization). Indeed, consider two solutions $\left(w_{1}, z_{1}\right)$ and $\left(w_{2}, z_{2}\right)$. Then
$$
\begin{aligned}
\frac{\mathrm{d}}{\mathrm{~d} s}\left(\frac{1}{2}\left\|z_{1}(s)-z_{2}(s)\right\|_{M}^{2}\right)= & \left\langle M\left(z_{1}(s)-z_{2}(s)\right), \frac{\mathrm{d} z_{1}}{\mathrm{~d} s}(s)-\frac{\mathrm{d} z_{2}}{\mathrm{~d} s}(s)\right\rangle \\
= & \left\langle w_{1}(s)-w_{2}(s), \frac{\mathrm{d} z_{1}}{\mathrm{~d} s}(s)-\frac{\mathrm{d} z_{2}}{\mathrm{~d} s}(s)\right\rangle \\
= & \left\langle w_{1}(s), \frac{\mathrm{d} z_{1}}{\mathrm{~d} s}(s)\right\rangle+\left\langle w_{2}(s), \frac{\mathrm{d} z_{2}}{\mathrm{~d} s}(s)\right\rangle \\
& -\left\langle w_{1}(s), \frac{\mathrm{d} z_{2}}{\mathrm{~d} s}(s)\right\rangle-\left\langle w_{2}(s), \frac{\mathrm{d} z_{1}}{\mathrm{~d} s}(s)\right\rangle
\end{aligned}
$$
By the properties of the LCP with derivatives, we have
$$
\left\langle w_{1}(s), \frac{\mathrm{d} z_{1}}{\mathrm{~d} s}(s)\right\rangle=\left\langle w_{2}(s), \frac{\mathrm{d} z_{2}}{\mathrm{~d} s}(s)\right\rangle=0 .
$$

Moreover, as $w_{1}(s), w_{2}(s) \geqslant 0$ and $\frac{\mathrm{d} z_{1}}{\mathrm{~d} s}(s), \frac{\mathrm{d} z_{2}}{\mathrm{~d} s}(s) \geqslant 0$, we have
$$
-\left\langle w_{1}(s), \frac{\mathrm{d} z_{2}}{\mathrm{~d} s}(s)\right\rangle-\left\langle w_{2}(s), \frac{\mathrm{d} z_{1}}{\mathrm{~d} s}(s)\right\rangle \leqslant 0 .
$$
Thus $\left\|z_{1}(s)-z_{2}(s)\right\|_{M}^{2}$ is decreasing. This proves that the solution of the LCP with derivatives is unique up to initialization. This uniqueness enables to identify the solution of the parametric LCP with the solution of the LCP with derivatives.

Conclusion. We have sketched the connections between the main objects of the proof. This sketch should help to interpret the results of Sec. 3 (and consequently of Sec. 2). The fact that the rescaled time $s$ plays the role of an inverse regularization parameter $\mu$ is particularly clear from a comparison between the parametric LCP and the LCP with derivatives. Further, the monotonicity assumption on the lasso regularization path is required to make a connection between the parametric LCP and the LCP with derivatives. Finally, we obtain a result on the averaged trajectory (and not trajectory itself) because the LCP with derivatives is obtained by integrating the DLN dynamics.

However, this proof sketch hides several technical challenges. First, $M$ is not assumed to be invertible, which breaks the uniqueness of the solution of the LCP and of the LCP with derivatives. Second, the proof sketch uses informal approximate symbols to deal with asymptotics when $\varepsilon \rightarrow 0$. Making these approximations rigorous requires significant additional work. Finally, we deal directly with the nonmonotone case of Thm. 3.2 (which requires to control the deviation from the proof sketch above), and then deduce Thm. 3.1 as a corollary.

We provide the detailed and rigorous proofs below.

\subsection*{4.2 Mirror flow interpretation}

We recall the interpretation of the DLN dynamics as a mirror flow [23]. Eq. (3.3) can be interpreted as a mirror flow
$$
\begin{equation*}
\frac{\mathrm{d} \nabla h\left(x^{\varepsilon}\right)}{\mathrm{d} t}=-\nabla \widetilde{L}\left(x^{\varepsilon}\right), \tag{4.1}
\end{equation*}
$$
where $\widetilde{L}(x)=\ell(x)+\lambda\langle\mathbb{1}, x\rangle$ and the mirror map
$$
h(x)=\frac{1}{4} \sum_{i=1}^{d}\left(x_{i} \log x_{i}-x_{i}\right)
$$
is the entropy of the vector $x>0$.
A central tool in analyzing mirror flows is the Bregman divergence associated to the mirror map $h$. For $x, y>0$, it is defined as
$$
\begin{align*}
D(x, y) & =h(x)-h(y)-\langle\nabla h(y), x-y\rangle \\
& =\frac{1}{4} \sum_{i=1}^{d}\left(x_{i} \log \frac{x_{i}}{y_{i}}-x_{i}+y_{i}\right) . \tag{4.2}
\end{align*}
$$

Note that, by convexity of the mirror map $h$, the Bregman divergence $D$ is always nonnegative. In our case, this Bregman divergence can be interpreted as a relative entropy.

The mirror variable $\nabla h\left(x^{\varepsilon}\right)$ has an initialization $\nabla h\left(x^{\varepsilon}(0)\right)$ that is diverging as $\varepsilon \rightarrow 0$ :
$$
\nabla h\left(x^{\varepsilon}(0)\right)=\frac{1}{4} \log x^{\varepsilon}(0)=-\frac{1}{4}\left(\log \frac{1}{\varepsilon}\right) \mathbb{1}+O(1) .
$$
For this reason, we define a rescaled mirror variable
$$
w^{\varepsilon}(s)=-\frac{4}{\log \frac{1}{\varepsilon}} \nabla h\left(x^{\varepsilon}(s)\right)=-\frac{1}{\log \frac{1}{\varepsilon}} \log x^{\varepsilon}(s) .
$$
We have $w^{\varepsilon}(0) \xrightarrow[\varepsilon \rightarrow 0]{ } \mathbb{1}$. This rescaled version particularly fits the analysis in the rescaled time $s$. For instance,
$$
\begin{equation*}
\frac{\mathrm{d} w^{\varepsilon}}{\mathrm{d} s}=-\frac{4}{\log \frac{1}{\varepsilon}} \frac{\mathrm{~d} t}{\mathrm{~d} s} \frac{\mathrm{~d} \nabla h\left(x^{\varepsilon}\right)}{\mathrm{d} t} \underset{(\text { Eq. (4.1)) }}{=} \nabla \widetilde{L}\left(x^{\varepsilon}\right)=M x^{\varepsilon}-r+\lambda \mathbb{1} . \tag{4.3}
\end{equation*}
$$

\subsection*{4.3 Uniform bound on the trajectories}

The goal of this section is to prove that the trajectories $x^{\varepsilon}(t)$ of the DLN dynamics are bounded uniformly in $t \geqslant 0$ and sufficiently small $\varepsilon>0$.

Proposition 4.1. There exists $C=C(d, M, r, \lambda, \alpha)>0$ and $\varepsilon_{0}=\varepsilon_{0}(\alpha)>0$ such that
$$
\forall \varepsilon \in\left(0, \varepsilon_{0}\right), \forall t \geqslant 0, \quad\left\|x^{\varepsilon}(t)\right\| \leqslant C .
$$

To prove this result, we first note that as the DLN dynamics are a gradient flow, the function values must be nonincreasing along trajectories.

Lemma 4.2. For all $\varepsilon>0, t \mapsto \widetilde{L}\left(x^{\varepsilon}(t)\right)$ is nonincreasing. As a consequence, there exists $C=C(M, r, \lambda, \alpha)>0$ such that for all $0<\varepsilon \leqslant 1$, for all $t \geqslant 0$, $\widetilde{L}\left(x^{\varepsilon}(t)\right) \leqslant C$.

Proof. Using Eq. (3.3),
$$
\frac{\mathrm{d}}{\mathrm{~d} t}\left(\widetilde{L}\left(x^{\varepsilon}\right)\right)=\sum_{i=1}^{d} \partial_{i} \widetilde{L}\left(x^{\varepsilon}\right) \frac{\mathrm{d} x_{i}^{\varepsilon}}{\mathrm{d} t}=-4 \sum_{i=1}^{d} x_{i}^{\varepsilon}\left(\partial_{i} \widetilde{L}\left(x^{\varepsilon}\right)\right)^{2} \leqslant 0 .
$$
This proves that $t \mapsto \widetilde{L}\left(x^{\varepsilon}(t)\right)$ is nonincreasing.
Moreover, the continuous function $\widetilde{L}$ is bounded by a constant $C=C(M, r, \lambda, \alpha)$ on the compact interval $\left\{\kappa \alpha^{2}, \kappa \in[0,1]\right\} \subset \mathbb{R}^{d}$. As a consequence, for all $0<\varepsilon \leqslant 1$, for all $t \geqslant 0$,
$$
\widetilde{L}\left(x^{\varepsilon}(t)\right) \leqslant \widetilde{L}\left(x^{\varepsilon}(0)\right)=\widetilde{L}\left(\varepsilon \alpha^{2}\right) \leqslant C .
$$ \(\square\)

If $\lambda>0$ or $M$ is positive definite, the function $\widetilde{L}$ is coercive on the set of nonnegative vectors, thus Lemma 4.2 implies Prop. 4.1. However, the proof when $\lambda=0$ and $M$ is not positive definite requires more work. We now assume that we are in this case. Lemma 4.2 only implies a bound on $M x^{\varepsilon}(t)$.

Lemma 4.3. There exists $C=C(M, r, \alpha)>0$ such that for all $0<\varepsilon \leqslant 1$, for all $t \geqslant 0,\left\|M x^{\varepsilon}(t)\right\| \leqslant C$.

Proof. Let $x_{*}=x_{*}(r, M)$ be the minimum norm minimizer of $\ell$. Then for any $x \in \mathbb{R}^{d}$,
$$
\begin{aligned}
\|M x\|^{2} & \leqslant\|M\|\left\|M^{1 / 2} x\right\|^{2} \leqslant 2\|M\|\left(\left\|M^{1 / 2} x_{*}\right\|^{2}+\left\|M^{1 / 2}\left(x-x_{*}\right)\right\|^{2}\right) \\
& =2\|M\|\left(\left\|M^{1 / 2} x_{*}\right\|^{2}+2 \ell(x)-2 \ell\left(x_{*}\right)\right) \\
& =2\|M\|\left(\left\|M^{1 / 2} x_{*}\right\|^{2}+2 \widetilde{L}(x)-2 \ell\left(x_{*}\right)\right) .
\end{aligned}
$$
By Lemma 4.2, there exists $C_{1}=C_{1}(M, r, \alpha)>0$ such that for all $0<\varepsilon \leqslant 1$, for all $t \geqslant 0, \widetilde{L}\left(x^{\varepsilon}(t)\right) \leqslant C_{1}$. Thus the lemma holds with
$$
C(M, r, \alpha)=2\|M\|\left(\left\|M^{1 / 2} x_{*}\right\|^{2}+2 C_{1}(M, r, \alpha)-2 \ell\left(x_{*}\right)\right) .
$$ \(\square\)

Our strategy consists in characterizing the flow $x^{\varepsilon}(t)$ from its image $M x^{\varepsilon}(t)$, and, as a consequence, showing that $x^{\varepsilon}(t)$ is bounded by a bound on its image $M x^{\varepsilon}(t)$. These arguments are the two lemmas below.

Lemma 4.4. For all $t \geqslant 0$,
$$
\begin{equation*}
x^{\varepsilon}(t)=\underset{x \geqslant 0, M x=M x^{\varepsilon}(t)}{\operatorname{argmin}} D\left(x, x^{\varepsilon}(0)\right), \tag{4.4}
\end{equation*}
$$
where $D(x, y)$ is defined in Eq. (4.2). Note that we extend $D(x, y)$ to coordinates $x_{i}=0$ by setting by continuity $0 \log 0=0$.

Proof. A point $x>0$ is a minimizer of $\min ._{x \geqslant 0, M x=M x^{\varepsilon}(t)} D\left(x, x^{\varepsilon}(0)\right)$ if and only if $M x=M x^{\varepsilon}(t)$ and $\nabla_{x} D\left(x, x^{\varepsilon}(0)\right) \in \operatorname{Span} M$. For $x=x^{\varepsilon}(t)>0$, only the second condition needs to be checked. As $\nabla_{x} D(x, y)=\nabla h(x)-\nabla h(y)$ and by Eq. (4.1), we have
$$
\begin{aligned}
\nabla_{x} D\left(x^{\varepsilon}(t), x^{\varepsilon}(0)\right) & =\nabla h\left(x^{\varepsilon}(t)\right)-\nabla h\left(x^{\varepsilon}(0)\right) \\
& =\int_{0}^{t}\left(r-M x^{\varepsilon}\left(t^{\prime}\right)\right) \mathrm{d} t^{\prime} \in \operatorname{Span} M .
\end{aligned}
$$
Moreover, $x^{\varepsilon}(t)$ is the unique minimizer as $D(.,$.$) is marginally strictly convex$ in its first variable. This justifies using the notation argmin. This concludes the proof. \(\square\)

Lemma 4.5. There exists $\varepsilon_{0}=\varepsilon_{0}(\alpha)>0$ and $C=C(d, M)>0$ such that for all $0<\varepsilon \leqslant \varepsilon_{0}$, for all $y=M u$ for some $u \in \mathbb{R}^{d}, u \geqslant 0$, denoting
$$
\begin{equation*}
x(y)=\underset{x \geqslant 0, M x=y}{\operatorname{argmin}} D\left(x, x^{\varepsilon}(0)\right), \tag{4.5}
\end{equation*}
$$
we have
$$
\|x(y)\| \leqslant C\left(1+\|y\|^{2}\right) .
$$

Before we prove this last lemma, let us combine the above lemmas to prove Prop. 4.1.

Proof of Proposition 4.1. By Lemma 4.4,
$$
\begin{equation*}
x^{\varepsilon}(t)=\underset{x>0, M x=M x^{\varepsilon}(t)}{\operatorname{argmin}} D\left(x, x^{\varepsilon}(0)\right) . \tag{4.6}
\end{equation*}
$$
Using Lemma 4.5 and then Lemma 4.3, there exists $\varepsilon_{0}=\varepsilon_{0}(\alpha)>0$ such that for all $0<\varepsilon<\varepsilon_{0}$,
$$
\left\|x^{\varepsilon}(t)\right\| \leqslant C(d, M)\left(1+\left\|M x^{\varepsilon}(t)\right\|^{2}\right) \leqslant C(d, M, r, \alpha) .
$$ \(\square\)

We are now only left with the proof of Lemma 4.5 to finish this section. This result requires a Caratheodory theorem on cones. Let $a_{i}, i \in I$, denote a finite family of vectors in $\mathbb{R}^{d}$. The cone generated by $\left(a_{i}\right)_{i \in I}$ is defined as
$$
\operatorname{Cone}\left(a_{i}, i \in I\right)=\left\{\sum_{i \in I} \lambda_{i} a_{i} \mid \lambda_{i} \geqslant 0, i \in I\right\} .
$$

Theorem 4.6 ([7]). Let $a_{1}, \ldots, a_{k} \in \mathbb{R}^{d}$ and $y \in \operatorname{Cone}\left(a_{1}, \ldots, a_{k}\right)$.
There exists a linearly independent subfamily $a_{i}, i \in I, I \subset\{1, \ldots, k\}$ such that $y \in \operatorname{Cone}\left(a_{i}, i \in I\right)$.

In particular, $y$ is in the cone generated by a subfamily of at most $d$ vectors.
To be precise, Carathéodory's theorem usually refers to the last statement. However, below, we are interested in the linear independence statement, which follows easily from the same proof.

Proof. As $y \in \operatorname{Cone}\left(a_{1}, \ldots, a_{k}\right), y$ can be decomposed as $y=\sum_{i \in I} \lambda_{i} a_{i}$ with $I \subset\{1, \ldots, k\}$ and $\lambda_{i} \geqslant 0, i \in I$. Consider such a decomposition with $I$ of minimal cardinality. We will show that in this case, the $a_{i}, i \in I$ are linearly independent.

By contradiction, assume that there exists $\mu_{i}, i \in I$, not all equal to 0 , such that $\sum_{i \in I} \mu_{i} a_{i}=0$. Then for all $t$, we have that $y=\sum_{i \in I}\left(\lambda_{i}-t \mu_{i}\right) a_{i}$. We will use this degree of freedom in $t$ to remove an element from $I$, and thus contradict the minimality of $I$.

Without loss of generality, we can assume that there exists a positive $\mu_{i}$. (We can consider $-\mu$ instead of $\mu$.) Consider
$$
\tau=\inf \left\{t \geqslant 0 \mid \lambda_{i}-t \mu_{i}=0 \text { for some } i \in I\right\} .
$$
Note that $\tau<\infty$ as there exists $i \in I$ such that $\mu_{i}>0$. Then for all $i \in I$, $\lambda_{i}-\tau \mu_{i} \geqslant 0$, with equality for at least one $i \in I$, that we denote $i_{0}$. Then $y=$ $\sum_{i \in I \backslash\left\{i_{0}\right\}}\left(\lambda_{i}-\tau \mu_{i}\right) a_{i}$. Thus $I$ is not minimal, which gives a contradiction. \(\square\)

We now use Caratheodory's theorem to show a central lemma. Let us give first the motivation. Consider a feasible linear system $A x=y$. The minimum norm solution $x=A^{\dagger} y$ is bounded in norm by $\left\|A^{\dagger}\right\|\|y\|$. We now consider the same question for the system $A x=y$ with the additional constraint $x \geqslant 0$ (assuming there exists at least one such solution). How can the minimum norm solution be bounded? Carathéodory's theorem enables to prove that, the nonnegative minimum norm solution is, again, bounded by a constant proportional to the norm of $y$.

Lemma 4.7. Let $A \in \mathbb{R}^{d \times k}$. There exists $C=C(A)>0$ such that for all $y=A u$ for some $u \in \mathbb{R}^{k}, u \geqslant 0$, denoting
$$
\begin{equation*}
x(y)=\underset{x \geqslant 0, A x=y}{\operatorname{argmin}}\|x\|, \tag{4.7}
\end{equation*}
$$
we have
$$
\|x(y)\| \leqslant C\|y\| .
$$
Proof. First, we note that $\|x\|$ diverges as $\|x\| \rightarrow \infty, x \geqslant 0, A x=y$. As a consequence, the minimizer in Eq. (4.5) is well-defined as the unique minimizer of a strictly convex function on a compact set.

In this proof, we show that the lemma holds with $C:=\max _{I \subset\{1, \ldots, k\}}\left\|\left(A_{I}\right)^{\dagger}\right\|$. Denote $a_{1}, \ldots, a_{k}$ the columns of $A$. Let $y=A u$ for some $u \geqslant 0$. Then $y \in \operatorname{Cone}\left(a_{1}, \ldots, a_{k}\right)$. By Caratheodory's theorem, there exists a linearly independent subfamily $a_{i}, i \in I$, such that $y \in \operatorname{Cone}\left(a_{i}, i \in I\right)$, i.e., $y=A_{I} v$ for some $v \in \mathbb{R}^{I}, v \geqslant 0$. The matrix $A_{I}$ has full column rank, thus $v=\left(A_{I}\right)^{\dagger} y$. Consider $x \in \mathbb{R}^{k}$ such that $x_{i}=v_{i}$ if $i \in I$, and $x_{i}=0$ otherwise. Then $A x=y$ and $x \geqslant 0$. Thus
$$
\|x(y)\| \leqslant\|x\|=\|v\|=\left\|\left(A_{I}\right)^{\dagger} y\right\| \leqslant\left\|\left(A_{I}\right)^{\dagger}\right\|\|y\| \leqslant C\|y\| .
$$
This completes the proof. \(\square\)

We are now ready to prove Lemma 4.5.
Proof of Lemma 4.5. First, we note that $D\left(x, x^{\varepsilon}(0)\right)$ diverges as $\|x\| \rightarrow \infty$, $x \geqslant 0$. As a consequence, the minimizer in Eq. (4.5) is well-defined as the unique minimizer of a strictly convex function on a compact set.

The only difference between Lemma 4.5 and Lemma 4.7 is that the former minimizes $D\left(x, x^{\varepsilon}(0)\right)$ while the latter minimizes $\|x\|$. However, the two
quantities are comparable in the sense that there exists $0<\varepsilon_{0}=\varepsilon_{0}(\alpha)<1$, $C_{1}=C_{1}(d), C_{2}=C_{2}(d)>0$ such that for all $0<\varepsilon \leqslant \varepsilon_{0}$, for all $x \geqslant 0$,
$$
\begin{equation*}
\frac{1}{8}\left(\log \frac{1}{\varepsilon}\right)\|x\|-C_{1} \leqslant D\left(x, x^{\varepsilon}(0)\right) \leqslant C_{2}\left(\log \frac{1}{\varepsilon}\right)\|x\|+\frac{1}{4}\|x\|^{2}+1 . \tag{4.8}
\end{equation*}
$$
Indeed,
$$
\begin{aligned}
D\left(x, x^{\varepsilon}(0)\right) & =\frac{1}{4} \sum_{i=1}^{d}\left(x_{i} \log \frac{x_{i}}{\varepsilon \alpha_{i}^{2}}-x_{i}+\varepsilon \alpha_{i}^{2}\right) \\
& =\frac{1}{4} \sum_{i=1}^{d} x_{i} \log x_{i}+\frac{1}{4}\left(\log \frac{1}{\varepsilon}-1\right)\|x\|_{1}+\frac{1}{4} \sum_{i=1}^{d} x_{i} \log \frac{1}{\alpha_{i}^{2}}+\frac{\varepsilon}{4} \sum_{i=1}^{d} \alpha_{i}^{2} .
\end{aligned}
$$
For the lower-bound, we use that $u \mapsto u \log u$ is bounded from below on $\mathbb{R}_{\geqslant 0}$. Thus there exists $0<\varepsilon_{1}=\varepsilon_{1}(\alpha)<1$ such that, for all $\varepsilon<\varepsilon_{1}$,
$$
D\left(x, x^{\varepsilon}(0)\right) \geqslant-C_{1}(d)+\frac{1}{8}\left(\log \frac{1}{\varepsilon}\right)\|x\| .
$$
For the upper-bound, we have
$$
\begin{aligned}
D\left(x, x^{\varepsilon}(0)\right) & =\frac{1}{4} \sum_{i=1}^{d}\left(x_{i} \log \frac{x_{i}}{\varepsilon \alpha_{i}^{2}}-x_{i}+\varepsilon \alpha_{i}^{2}\right) \\
& \leqslant \frac{1}{4} \sum_{i=1}^{d} x_{i}\left(\log x_{i}+\log \frac{1}{\varepsilon}+\log \frac{1}{\alpha_{i}^{2}}\right)+\frac{\varepsilon}{4} \sum_{i=1}^{d} \alpha_{i}^{2} .
\end{aligned}
$$
We use $\log y \leqslant y$ for $y>0$. Thus there exists $0<\varepsilon_{2}=\varepsilon_{2}(\alpha)<1, C_{2}=C_{2}(d)$ such that, for all $\varepsilon<\varepsilon_{2}$,
$$
D\left(x, x^{\varepsilon}(0)\right) \leqslant \frac{1}{4}\|x\|^{2}+\frac{1}{2}\left(\log \frac{1}{\varepsilon}\right) \sum_{i=1}^{d} x_{i}+1 \leqslant \frac{1}{4}\|x\|^{2}+C_{2}(d)\left(\log \frac{1}{\varepsilon}\right)\|x\|+1 .
$$
Thus Eq. (4.8) holds for $\varepsilon \leqslant \varepsilon_{0}(\alpha):=\min \left(\varepsilon_{1}(\alpha), \varepsilon_{2}(\alpha)\right)$.
We now define $\beta(y)=\operatorname{argmin}_{\beta \geqslant 0, M \beta=y}\|\beta\|$. By Lemma 4.7, $\|\beta(y)\| \leqslant$ $C_{3}(M)\|y\|$. Then we have,
$$
\begin{aligned}
\frac{1}{8}\left(\log \frac{1}{\varepsilon}\right)\|x(y)\| & \leqslant C_{1}(d)+D\left(x(y), x^{\varepsilon}(0)\right) \quad \text { by Eq. (4.8) } \\
& \leqslant C_{1}(d)+D\left(\beta(y), x^{\varepsilon}(0)\right) \quad \text { by the variational definition of } x(y) \\
& \leqslant C_{4}(d)+C_{2}(d)\left(\log \frac{1}{\varepsilon}\right)\|\beta(y)\|+\frac{1}{4}\|\beta(y)\|^{2} \quad \text { by Eq. (4.8) } \\
& \leqslant C_{4}(d)+C_{5}(d, M)\left(\log \frac{1}{\varepsilon}\right)\|y\|+C_{6}(d, M)\|y\|^{2} .
\end{aligned}
$$
Assuming that $\varepsilon_{0}$ is small enough so that $\frac{1}{8} \log \frac{1}{\varepsilon_{0}} \geqslant 1$, we have
$$
\|x(y)\| \leqslant C_{4}(d)+8 C_{5}(d, M)\|y\|+C_{6}(d, M)\|y\|^{2} \leqslant C(d, M)\left(1+\|y\|^{2}\right) .
$$ \(\square\)

\subsection*{4.4 The positive lasso and linear complementarity problems}

The positive lasso (3.4) is in fact a constrained quadratic optimization problem: $\min _{. x \geqslant 0} \frac{1}{2}\langle x, M x\rangle-\langle r, x\rangle+\left(\lambda+\frac{1}{\mu}\right)\langle\mathbb{1}, x\rangle$. As a consequence, its primal-dual formulation is a linear complementarity problem [12].

Proposition 4.8. Let $x \in \mathbb{R}^{d}$. The vector $x$ is a minimizer of the optimization problem (3.4) if and only if there exists $v \in \mathbb{R}^{d}$ such that $(v, x)$ is a solution of
$$
\begin{align*}
& v=-r+\left(\lambda+\frac{1}{\mu}\right) \mathbb{1}+M x  \tag{4.9}\\
& v \geqslant 0, x \geqslant 0,\langle v, x\rangle=0
\end{align*}
$$
The system above has the form of a linear complementarity problem (LCP) [12].

This result is classical and its proof follows from convex duality, see [6], Sec. 5. We recall it for the sake of completeness.

Proof. For simplicity, we denote $q=-r+\left(\lambda+\frac{1}{\mu}\right) \mathbb{1}$. The Lagrangian associated to (3.4) is
$$
L(x, v)=\operatorname{Lasso}(x, \mu)-\langle v, x\rangle=\frac{1}{2}\langle x, M x\rangle+\langle q, x\rangle-\langle v, x\rangle
$$
where $v \in \mathbb{R}^{d}$ is the Lagrange multiplier associated to the constraint $x \geqslant 0$. As the optimization problem (3.4) is convex, the KKT conditions are necessary and sufficient for optimality. The stationarity condition is
$$
0=\nabla_{x} L(x, v)=q+M x-v,
$$
the feasibility conditions are $x \geqslant 0$ and $v \geqslant 0$, and the complementary slackness condition is $\langle v, x\rangle=0$. This proves Prop. 4.8. \(\square\)

We now study the existence and uniqueness of the solution of the LCP (4.9). Note that if $M$ is positive definite, there exists a unique solution $(v, x)$, see [12], Thm. 3.1.6. In the more general case where $M$ is positive semidefinite, existence still holds but uniqueness is more subtle. For instance, the positive lasso (3.4) might not have a unique minimizer, thus we might not have uniqueness of the solution in $x$. However, we have uniqueness in $v$.

Proposition 4.9. There exists a solution of the LCP (4.9). Moreover, the solution of the LCP is unique in $v$ in the sense that if $(v, x)$ and $\left(v^{\prime}, x^{\prime}\right)$ are two solutions of the LCP, then $v=v^{\prime}$.

Proof. Existence. By [13], it suffices to show that
$$
\operatorname{Lasso}(x, \mu)=\ell(x)+\left(\lambda+\frac{1}{\mu}\right)\langle\mathbb{1}, x\rangle
$$
is bounded from below on the set $\{x \mid x \geqslant 0\}$. The first term $\ell(x)$ is bounded from below on $\mathbb{R}^{d}$ (as $r \in \operatorname{Span}(M)$ ), and the second term is nonnegative on $\{x \mid x \geqslant 0\}$.

Uniqueness. The result is provided in [12], Thm. 3.1.7(d). \(\square\)

\subsection*{4.5 The positive lasso regularization path and parametric linear complementarity problems}

In Sec. 3, we consider a solution $x(\mu)$ of the positive lasso with varying inverse regularization parameter $\mu>0$. This describes the lasso regularization path. In this section, we draw a connection with so-called parametric LCPs.

From Prop. 4.8, there exists $v(\mu)$ such that $(v(\mu), x(\mu))$ is a solution of the LCP
$$
\begin{align*}
& v(\mu)=-r+\left(\lambda+\frac{1}{\mu}\right) \mathbb{1}+M x(\mu),  \tag{4.10}\\
& v(\mu) \geqslant 0, x(\mu) \geqslant 0,\langle v(\mu), x(\mu)\rangle=0 .
\end{align*}
$$
Denote $w(\mu)=\mu v(\mu)$ and $z(\mu)=\mu x(\mu)$. Then
$$
\begin{align*}
& w(\mu)=-\mu r+(1+\mu \lambda) \mathbb{1}+M z(\mu) \\
& w(\mu) \geqslant 0, z(\mu) \geqslant 0,\langle w(\mu), z(\mu)\rangle=0 \tag{4.11}
\end{align*}
$$
This is a parametric LCP, where the parameter is $\mu$, see [12], Sec. 4.5.
Note that while the LCP (4.10) is defined only for $\mu>0$, the LCP (4.11) is also defined for $\mu=0$. This extension is rather trivial, the solution of both LCPs being simple for $\mu$ small enough, as shown in the following lemma.
Lemma 4.10. Assume $0 \leqslant \mu<\frac{1}{\max \left(\|r-\lambda \mathbb{1}\|_{\infty}, 1\right)}$. Then the LCP (4.11) has a unique solution $(w(\mu), z(\mu))=((1+\mu \lambda) \mathbb{1}-\mu r, 0)$. If further $\mu>0$, this means that the LCP (4.10) has a unique solution $(v(\mu), x(\mu))=\left(-r+\left(\lambda+\frac{1}{\mu}\right) \mathbb{1}, 0\right)$.
Proof. $(w(\mu), z(\mu))=((1+\mu \lambda) \mathbb{1}-\mu r, 0)$ is a solution of (4.11). As the solution is unique in $w,(1+\mu \lambda) \mathbb{1}-\mu r$ is the unique solution in $w$. But as $(1+\mu \lambda) \mathbb{1}-\mu r>0$, this imposes that $z(\mu)=0$ is the unique solution in $z$ by complementarity. \(\square\)

We now prove a regularity result on the solution of the parametric LCP (4.11).
Lemma 4.11. Let $w(\mu)$ be the unique solution in $w$ of the parametric LCP (4.11). Then $\mu \geqslant 0 \mapsto w(\mu)$ is absolutely continuous, $\frac{\mathrm{d}}{\mathrm{d} \mu}\left(\frac{1}{1+\mu \lambda} w(\mu)\right) \in \operatorname{Span} M$ and $\left\|\frac{\mathrm{d}}{\mathrm{d} \mu}\left(\frac{1}{1+\mu \lambda} w(\mu)\right)\right\|_{M^{\dagger}} \leqslant\|r\|_{M^{\dagger}}$.
Proof. Let $\mu, \mu^{\prime} \geqslant 0$ and $(w, z)=(w(\mu), z(\mu)),\left(w^{\prime}, z^{\prime}\right)=\left(w\left(\mu^{\prime}\right), z\left(\mu^{\prime}\right)\right)$ denote solutions of the parametric LCP (4.11) for the respective values $\mu, \mu^{\prime}$. Then, we have
$$
\begin{aligned}
\frac{1}{1+\mu \lambda} w & =-\frac{\mu}{1+\mu \lambda} r+\mathbb{1}+M \frac{1}{1+\mu \lambda} z \\
\frac{1}{1+\mu^{\prime} \lambda} w^{\prime} & =-\frac{\mu^{\prime}}{1+\mu^{\prime} \lambda} r+\mathbb{1}+M \frac{1}{1+\mu^{\prime} \lambda} z^{\prime}
\end{aligned}
$$

Hence,
$$
\begin{aligned}
\frac{1}{1+\mu \lambda} w-\frac{1}{1+\mu^{\prime} \lambda} w^{\prime} & =-\left(\frac{\mu}{1+\mu \lambda}-\frac{\mu^{\prime}}{1+\mu^{\prime} \lambda}\right) r+M\left(\frac{1}{1+\mu \lambda} z-\frac{1}{1+\mu^{\prime} \lambda} z^{\prime}\right) \\
& \in \operatorname{Span} M
\end{aligned}
$$
and
$$
\begin{aligned}
& \left\|\frac{1}{1+\mu \lambda} w-\frac{1}{1+\mu^{\prime} \lambda} w^{\prime}\right\|_{M^{\dagger}}^{2} \\
& =\left\langle\frac{1}{1+\mu \lambda} w-\frac{1}{1+\mu^{\prime} \lambda} w^{\prime},-\left(\frac{\mu}{1+\mu \lambda}-\frac{\mu^{\prime}}{1+\mu^{\prime} \lambda}\right) r\right. \\
& \left.\quad+M\left(\frac{1}{1+\mu \lambda} z-\frac{1}{1+\mu^{\prime} \lambda} z^{\prime}\right)\right\rangle_{M^{\dagger}} \\
& =-\left(\frac{\mu}{1+\mu \lambda}-\frac{\mu^{\prime}}{1+\mu^{\prime} \lambda}\right)\left\langle\frac{1}{1+\mu \lambda} w-\frac{1}{1+\mu^{\prime} \lambda} w^{\prime}, r\right\rangle_{M^{\dagger}} \\
& \quad+\left\langle\frac{1}{1+\mu \lambda} w-\frac{1}{1+\mu^{\prime} \lambda} w^{\prime}, \frac{1}{1+\mu \lambda} z-\frac{1}{1+\mu^{\prime} \lambda} z^{\prime}\right\rangle \\
& =-\left(\frac{\mu}{1+\mu \lambda}-\frac{\mu^{\prime}}{1+\mu^{\prime} \lambda}\right)\left\langle\frac{1}{1+\mu \lambda} w-\frac{1}{1+\mu^{\prime} \lambda} w^{\prime}, r\right\rangle_{M^{\dagger}} \\
& \quad+\frac{1}{(1+\mu \lambda)^{2}}\langle w, z\rangle-\frac{1}{(1+\mu \lambda)\left(1+\mu^{\prime} \lambda\right)}\left\langle w, z^{\prime}\right\rangle \\
& \quad-\frac{1}{(1+\mu \lambda)\left(1+\mu^{\prime} \lambda\right)}\left\langle w^{\prime}, z\right\rangle+\frac{1}{\left(1+\mu^{\prime} \lambda\right)^{2}}\left\langle w^{\prime}, z^{\prime}\right\rangle
\end{aligned}
$$
We can use Hölder's inequality to bound the first term. Furthermore, by complementarity slackness $\langle z, w\rangle=\left\langle z^{\prime}, w^{\prime}\right\rangle=0$. Finally, all vectors $w, w^{\prime}, z, z^{\prime}$ are nonnegative, thus $\left\langle w^{\prime}, z\right\rangle,\left\langle w, z^{\prime}\right\rangle \geqslant 0$. Thus, we have
$$
\begin{aligned}
& \left\|\frac{1}{1+\mu \lambda} w-\frac{1}{1+\mu^{\prime} \lambda} w^{\prime}\right\|_{M^{\dagger}}^{2} \\
& \quad \leqslant\left|\frac{\mu}{1+\mu \lambda}-\frac{\mu^{\prime}}{1+\mu^{\prime} \lambda}\right|\left\|\frac{1}{1+\mu \lambda} w-\frac{1}{1+\mu^{\prime} \lambda} w^{\prime}\right\|_{M^{\dagger}}\|r\|_{M^{\dagger}}
\end{aligned}
$$
As $\mu \mapsto \frac{\mu}{1+\mu \lambda}$ is 1 -Lipschitz, we have
$$
\left\|\frac{1}{1+\mu \lambda} w-\frac{1}{1+\mu^{\prime} \lambda} w^{\prime}\right\|_{M^{\dagger}}^{2} \leqslant\left|\mu-\mu^{\prime}\right|\|r\|_{M^{\dagger}} .
$$
This proves that the map $\mu \mapsto \frac{1}{1+\mu \lambda} w(\mu)$ is Lipschitz continuous, thus absolutely continuous. Thus $\mu \mapsto w(\mu)$ is also absolutely continuous. As for all $\mu, \mu^{\prime}$, $\frac{1}{1+\mu \lambda} w-\frac{1}{1+\mu^{\prime} \lambda} w^{\prime} \in \operatorname{Span} M$, we have $\frac{\mathrm{d}}{\mathrm{d} \mu}\left(\frac{1}{1+\mu \lambda} w(\mu)\right) \in \operatorname{Span} M$. The inequality above also shows that $\left\|\frac{\mathrm{d}}{\mathrm{d} \mu}\left(\frac{1}{1+\mu \lambda} w(\mu)\right)\right\|_{M^{\dagger}} \leqslant\|r\|_{M^{\dagger}}$. \(\square\)

\subsection*{4.6 Proof of Theorem 3.2}

For all $\mu>0, x(\mu)$ is a minimizer of $\min _{\cdot x \geqslant 0} \operatorname{Lasso}(x, \mu)$. We use the notations of Sec. 4.5: by Prop. 4.8, there exists $v(\mu)$ such that $(v(\mu), x(\mu))$ is a solution of the LCP (4.10). Denote $w(\mu)=\mu v(\mu)$ and $z(\mu)=\mu x(\mu)$. Then $(w(\mu), z(\mu))$ is a solution of the parametric LCP (4.11). We extend this definition of $(w, z)$ with $(w(0), z(0))=(\mathbb{1}, 0)$, which is a solution of the LCP (4.11) for $\mu=0$.

In this proof, the solution $(w(s), z(s))$ of the parametric LCP taken at $\mu=s$ will be compared to $\left(w^{\varepsilon}(s), z^{\varepsilon}(s)\right)$ where $w^{\varepsilon}(s)$ is defined in Sec. 4.2 and
$$
z^{\varepsilon}(s)=s \bar{x}^{\varepsilon}(s)=\int_{0}^{s} x^{\varepsilon}(u) \mathrm{d} u
$$
Note that
$$
\begin{equation*}
\frac{\mathrm{d} z^{\varepsilon}}{\mathrm{d} s}=x^{\varepsilon}(s) . \tag{4.12}
\end{equation*}
$$
Integrating Eq. (4.3), we obtain
$$
\begin{equation*}
w^{\varepsilon}(s)=w^{\varepsilon}(0)-s r+M z^{\varepsilon}(s)+s \lambda \mathbb{1} . \tag{4.13}
\end{equation*}
$$
This equation has a similarity with the first equation of the LCP (4.11).
We now seek to bound
$$
\Delta^{\varepsilon}(s):=\frac{1}{2}\left\|z^{\varepsilon}(s)-z(s)\right\|_{M}^{2} .
$$
At $s=0$, we have by definition, $z^{\varepsilon}(0)=0$ and by Lemma 4.10, $z(0)=0$. Thus $\Delta^{\varepsilon}(s)=0$.

We compute the derivative of $\Delta^{\varepsilon}(s)$ :
$$
\frac{\mathrm{d} \Delta^{\varepsilon}}{\mathrm{d} s}=\left\langle\frac{\mathrm{d} z^{\varepsilon}(s)}{\mathrm{d} s}-\frac{\mathrm{d} z(s)}{\mathrm{d} s}, M\left(z^{\varepsilon}(s)-z(s)\right)\right\rangle
$$
We use Eqs. (4.12), (4.13) and the first equation of (4.11):
$$
\begin{align*}
\frac{\mathrm{d} \Delta^{\varepsilon}}{\mathrm{d} s}= & \left\langle x^{\varepsilon}(s)-\frac{\mathrm{d} z(s)}{\mathrm{d} s}, w^{\varepsilon}(s)-w(s)+\mathbb{1}-w^{\varepsilon}(0)\right\rangle \\
= & \left\langle x^{\varepsilon}(s), w^{\varepsilon}(s)\right\rangle-\left\langle x^{\varepsilon}(s), w(s)\right\rangle-\left\langle\frac{\mathrm{d} z(s)}{\mathrm{d} s}, w^{\varepsilon}(s)\right\rangle  \tag{4.14}\\
& \quad+\left\langle\frac{\mathrm{d} z(s)}{\mathrm{d} s}, w(s)\right\rangle+\left\langle x^{\varepsilon}(s), \mathbb{1}-w^{\varepsilon}(0)\right\rangle-\left\langle\frac{\mathrm{d} z(s)}{\mathrm{d} s}, \mathbb{1}-w^{\varepsilon}(0)\right\rangle .
\end{align*}
$$
We now upper-bound each term separately:
\begin{itemize}
\item[-] The function $u>0 \mapsto u \log u$ is uniformly lower bounded by a universal constant thus
$$
\left\langle x^{\varepsilon}(s), w^{\varepsilon}(s)\right\rangle=-\frac{1}{\log \frac{1}{\varepsilon}} \sum_{i=1}^{d} x_{i}^{\varepsilon}(s) \log x_{i}^{\varepsilon}(s) \leqslant \frac{C(d)}{\log \frac{1}{\varepsilon}} .
$$
\end{itemize}
\begin{itemize}
\item[-] We have $x^{\varepsilon}(s) \geqslant 0$ and $w(s) \geqslant 0$ thus $-\left\langle x^{\varepsilon}(s), w(s)\right\rangle \leqslant 0$.
\item[-] If $\frac{\mathrm{d} z_{i}(s)}{\mathrm{d} s} \geqslant 0$, we use that by Prop. 4.1,
$$
w_{i}^{\varepsilon}(s)=-\frac{1}{\log \frac{1}{\varepsilon}} \log x_{i}^{\varepsilon}(s) \geqslant-\frac{C(d, M, r, \lambda, \alpha)}{\log \frac{1}{\varepsilon}} .
$$
If $\frac{\mathrm{d} z_{i}(s)}{\mathrm{d} s} \leqslant 0$, we use Eq. (4.3) and Prop. 4.1 to obtain
$$
w_{i}^{\varepsilon}(s) \leqslant C(d, M, r, \lambda, \alpha)(1+s) .
$$
Thus
$$
\begin{aligned}
& -\left\langle\frac{\mathrm{d} z(s)}{\mathrm{d} s}, w^{\varepsilon}(s)\right\rangle \\
& \quad \leqslant C(d, M, r, \lambda, \alpha) \sum_{i=1}^{d}\left[\frac{1}{\log \frac{1}{\varepsilon}}\left(\frac{\mathrm{~d} z_{i}(s)}{\mathrm{d} s}\right)_{+}+(1+s)\left(\frac{\mathrm{d} z_{i}(s)}{\mathrm{d} s}\right)_{-}\right] .
\end{aligned}
$$
Recall that
$$
z^{\downarrow}(s)=\sum_{i=1}^{d} \int_{0}^{s}(1+u)\left(\frac{\mathrm{d} z_{i}(u)}{\mathrm{d} u}\right)_{-} \mathrm{d} u .
$$
Denote also
$$
z^{\uparrow}(s)=\sum_{i=1}^{d} \int_{0}^{s}\left(\frac{\mathrm{~d} z_{i}(u)}{\mathrm{d} u}\right)_{+} \mathrm{d} u .
$$
With these notations, we can write
$$
-\left\langle\frac{\mathrm{d} z(s)}{\mathrm{d} s}, w^{\varepsilon}(s)\right\rangle \leqslant C(d, M, r, \lambda, \alpha)\left[\frac{1}{\log \frac{1}{\varepsilon}} \frac{\mathrm{~d} z^{\uparrow}(s)}{\mathrm{d} s}+\frac{\mathrm{d} z^{\downarrow}(s)}{\mathrm{d} s}\right] .
$$
\item[-] Let $i \in\{1, \ldots, d\}$. We show that $\frac{\mathrm{d} z_{i}(s)}{\mathrm{d} s} w_{i}(s)=0$. From Eqs. (4.11), we have $w_{i}(s) z_{i}(s)=0$. If $w_{i}(s)=0$, then the conclusion is obvious. Otherwise $z_{i}(s)=0$. Differentiating $w_{i}(s) z_{i}(s)=0$, we obtain $\frac{\mathrm{d} w_{i}(s)}{\mathrm{d} s} z_{i}(s)+w_{i}(s) \frac{\mathrm{d} z_{i}(s)}{\mathrm{d} s}=0$. As $z_{i}(s)=0$, this gives the desired conclusion. Thus, we have $\left\langle\frac{\mathrm{d} z(s)}{\mathrm{d} s}, w(s)\right\rangle=0$.
\item[-] Note that $\mathbb{1}-w^{\varepsilon}(0)=\mathbb{1}+\frac{1}{\log \frac{1}{\varepsilon}} \log x^{\varepsilon}(0)=\frac{2}{\log \frac{1}{\varepsilon}} \log |\alpha|$. This enables to bound the last two terms, using again Prop. 4.1.
\end{itemize}
We thus obtain that
$$
\frac{\mathrm{d} \Delta^{\varepsilon}(s)}{\mathrm{d} s} \leqslant C(d, M, r, \lambda, \alpha)\left[\frac{1}{\log \frac{1}{\varepsilon}}\left(1+\frac{\mathrm{d} z^{\uparrow}(s)}{\mathrm{d} s}\right)+\frac{\mathrm{d} z^{\downarrow}(s)}{\mathrm{d} s}\right],
$$
and thus
$$
\begin{equation*}
\Delta^{\varepsilon}(s) \leqslant C(d, M, r, \lambda, \alpha)\left[\frac{1}{\log \frac{1}{\varepsilon}}\left(s+z^{\uparrow}(s)\right)+z^{\downarrow}(s)\right] . \tag{4.15}
\end{equation*}
$$

At this point, we have bounded $\left\|z^{\varepsilon}(s)-z(s)\right\|_{M}^{2}$, or, equivalently, $\| \bar{x}^{\varepsilon}(s)-$ $x(s) \|_{M}^{2}$, where $x(s)$ is a minimizer of the positive lasso with inverse regularization $\mu=s$. However, as $M$ might not be positive definite, we can not conclude directly.

The positive lasso objective function $\operatorname{Lasso}(x, \mu)$ is a quadratic function on the set of nonnegative vectors $x \geqslant 0$ :
$$
\operatorname{Lasso}(x, \mu)=g_{\mu}(x):=\frac{1}{2}\langle x, M x\rangle-\langle r, x\rangle+\left(\lambda+\frac{1}{\mu}\right)\langle\mathbb{1}, x\rangle .
$$
As a consequence, we can compute $\operatorname{Lasso}\left(\bar{x}^{\varepsilon}(s), s\right)=g_{s}\left(\bar{x}^{\varepsilon}(s)\right)$ using the secondorder approximation of $g_{s}$ at $x(s)$ :
$$
\begin{aligned}
& \operatorname{Lasso}\left(\bar{x}^{\varepsilon}(s), s\right)-\operatorname{PosLasso}_{*}(s)=g_{s}\left(\bar{x}^{\varepsilon}(s)\right)-g_{s}(x(s)) \\
& \quad=\left\langle\nabla g_{s}(x(s)), \bar{x}^{\varepsilon}(s)-x(s)\right\rangle+\frac{1}{2}\left\|\bar{x}^{\varepsilon}(s)-x(s)\right\|_{M}^{2} \\
& \quad=\left\langle M x(s)-r+\left(\lambda+\frac{1}{s}\right) \mathbb{1}, \bar{x}^{\varepsilon}(s)-x(s)\right\rangle+\frac{1}{2}\left\|\bar{x}^{\varepsilon}(s)-x(s)\right\|_{M}^{2} \\
& \quad=\left\langle v(s), \bar{x}^{\varepsilon}(s)-x(s)\right\rangle+\frac{1}{2}\left\|\bar{x}^{\varepsilon}(s)-x(s)\right\|_{M}^{2} \\
& \quad=\frac{1}{s^{2}} E^{\varepsilon}(s)
\end{aligned}
$$
where $E^{\varepsilon}(s)=\left\langle w(s), z^{\varepsilon}(s)-z(s)\right\rangle+\Delta^{\varepsilon}(s)$. We compute
$$
\begin{aligned}
\frac{\mathrm{d}}{\mathrm{~d} s} & \left(\frac{1}{1+s \lambda} E^{\varepsilon}(s)\right)= \\
& \left\langle\frac{\mathrm{d}}{\mathrm{~d} s}\left(\frac{1}{1+s \lambda} w(s)\right), z^{\varepsilon}(s)-z(s)\right\rangle+\frac{1}{1+s \lambda}\left\langle w(s), x^{\varepsilon}(s)\right\rangle \\
& -\frac{1}{1+s \lambda}\left\langle w(s), \frac{\mathrm{d} z(s)}{\mathrm{d} s}\right\rangle+\frac{1}{1+s \lambda} \frac{\mathrm{~d} \Delta^{\varepsilon}(s)}{\mathrm{d} s}+\frac{\mathrm{d}}{\mathrm{~d} s}\left(\frac{1}{1+s \lambda}\right) \Delta^{\varepsilon}(s) .
\end{aligned}
$$
For the first term, we use the Cauchy-Schwarz inequality and Lemma 4.11. Moreover, several terms cancel out with the expression of the derivative of $\Delta^{\varepsilon}(s)$ in Eq. (4.14). The last term is nonpositive. We obtain
$$
\begin{aligned}
& \frac{\mathrm{d}}{\mathrm{~d} s}\left(\frac{1}{1+s \lambda} E^{\varepsilon}(s)\right) \leqslant\|r\|_{M^{\dagger}}\left\|z^{\varepsilon}(s)-z(s)\right\|_{M} \\
& +\frac{1}{1+s \lambda}\left[\left\langle x^{\varepsilon}(s), w^{\varepsilon}(s)\right\rangle-\left\langle\frac{\mathrm{d} z(s)}{\mathrm{d} s}, w^{\varepsilon}(s)\right\rangle\right. \\
& \left.\quad+\left\langle x^{\varepsilon}(s), \mathbb{1}-w^{\varepsilon}(0)\right\rangle-\left\langle\frac{\mathrm{d} z(s)}{\mathrm{d} s}, \mathbb{1}-w^{\varepsilon}(0)\right\rangle\right]
\end{aligned}
$$

All of these terms have been bounded above. We obtain
$$
\begin{aligned}
& \frac{\mathrm{d}}{\mathrm{~d} s}\left(\frac{1}{1+s \lambda} E^{\varepsilon}(s)\right) \\
& \quad \leqslant C(d, M, r, \lambda, \alpha)\left[\Delta^{\varepsilon}(s)^{1 / 2}+\frac{1}{1+s \lambda}\left(\frac{1}{\log \frac{1}{\varepsilon}}\left(1+\frac{\mathrm{d} z^{\uparrow}(s)}{\mathrm{d} s}\right)+\frac{\mathrm{d} z^{\downarrow}(s)}{\mathrm{d} s}\right)\right] \\
& \quad \leqslant C(d, M, r, \lambda, \alpha)\left[\Delta^{\varepsilon}(s)^{1 / 2}+\frac{1}{\log \frac{1}{\varepsilon}}\left(1+\frac{\mathrm{d} z^{\uparrow}(s)}{\mathrm{d} s}\right)+\frac{\mathrm{d} z^{\downarrow}(s)}{\mathrm{d} s}\right] .
\end{aligned}
$$
Integrating between 0 and $s$ and using Eq. (4.15), we obtain
$$
\begin{aligned}
E^{\varepsilon}(s) \leqslant C(d, M, r, \lambda, \alpha)(1+s \lambda) & {\left[s\left(\frac{1}{\log \frac{1}{\varepsilon}}\left(s+z^{\uparrow}(s)\right)+z^{\downarrow}(s)\right)^{1 / 2}\right.} \\
& \left.+\frac{1}{\log \frac{1}{\varepsilon}}\left(s+z^{\uparrow}(s)\right)+z^{\downarrow}(s)\right] .
\end{aligned}
$$
This allows us to conclude
$$
\begin{aligned}
& \limsup _{\varepsilon \rightarrow 0} \operatorname{Lasso}\left(\bar{x}^{\varepsilon}(s), s\right)-\operatorname{PosLasso}_{*}(s)=\limsup _{\varepsilon \rightarrow 0} \frac{1}{s^{2}} E^{\varepsilon}(s) \\
& \quad \leqslant C(d, M, r, \lambda, \alpha)(1+s \lambda)\left[\frac{z^{\downarrow}(s)^{1 / 2}}{s}+\frac{z^{\downarrow}(s)}{s^{2}}\right] \\
& \quad=C(d, M, r, \lambda, \alpha) \eta\left(\lambda, s, z^{\downarrow}(s)\right)
\end{aligned}
$$

\subsection*{4.7 Proof of Theorem 3.1}

Thm. 3.1 is an application of Thm. 3.2. However, to apply Thm. 3.2, we need to prove that $\mu \mapsto x(\mu)$ is absolutely continuous. This is proven in the following lemma (in combination with Lemma 4.10).
Lemma 4.12. Under the assumptions of Thm. 3.1, the function $\mu \geqslant 0 \mapsto z(\mu)$ is absolutely continuous on compact subsets of $[0,+\infty)$.
Proof. From Lemma 4.11, $\mu \geqslant 0 \mapsto w(\mu)$ is locally Lipschitz continuous. Using the linear relationship $\frac{1}{1+\mu \lambda} w(\mu)=-\frac{\mu}{1+\mu \lambda} r+\mathbb{1}+M \frac{1}{1+\mu \lambda} z(\mu)$, this implies that $\mu \geqslant 0 \mapsto P_{\text {Span } M} z(\mu)$ is locally Lipschitz continuous, where $\mathrm{P}_{\text {Span } M}$ denotes the orthogonal projection onto Span $M$.

Denote also $\mathrm{P}_{\operatorname{ker} M}$ denotes the orthogonal projection onto $\operatorname{ker} M$. We have the complementarity slackness $\langle w(\mu), z(\mu)\rangle=0$. Recall that $\frac{1}{1+\mu \lambda} w(\mu) \in \mathbb{1}+$ $\operatorname{Span} M$. Thus we obtain
$$
\begin{aligned}
0 & =\left\langle\frac{1}{1+\mu \lambda} w(\mu), z(\mu)\right\rangle \\
& =\left\langle\frac{1}{1+\mu \lambda} w(\mu), \mathrm{P}_{\text {Span } M} z(\mu)\right\rangle+\left\langle\frac{1}{1+\mu \lambda} w(\mu), \mathrm{P}_{\text {ker } M} z(\mu)\right\rangle \\
& =\left\langle\frac{1}{1+\mu \lambda} w(\mu), \mathrm{P}_{\text {Span } M} z(\mu)\right\rangle+\left\langle\mathbb{1}, \mathrm{P}_{\text {ker } M} z(\mu)\right\rangle
\end{aligned}
$$

As $\mu \geqslant 0 \mapsto \frac{1}{1+\mu \lambda} w(\mu)$ and $\mu \geqslant 0 \mapsto \mathrm{P}_{\text {Span } M} z(\mu)$ are locally Lipschitz continuous, the dot product $\mu \geqslant 0 \mapsto\left\langle\frac{1}{1+\mu \lambda} w(\mu), \mathrm{P}_{\text {Span } M} z(\mu)\right\rangle$ is also locally Lipschitz continuous. As a consequence, the above inequality implies that $\mu \geqslant 0 \mapsto\left\langle\mathbb{1}, \mathrm{P}_{\text {ker } M} z(\mu)\right\rangle$ is locally Lipschitz continuous.

Consider $\mu_{1} \leqslant \mu_{2}$. As $s \mapsto z(\mu)$ is monotone, we have
$$
\begin{aligned}
\left\|z\left(\mu_{2}\right)-z\left(\mu_{1}\right)\right\|_{1}= & \left\langle\mathbb{1}, z\left(\mu_{2}\right)-z\left(\mu_{1}\right)\right\rangle \\
= & \left\langle\mathbb{1}, \mathrm{P}_{\operatorname{Span} M} z\left(\mu_{2}\right)-\mathrm{P}_{\operatorname{Span} M} z\left(\mu_{1}\right)\right\rangle \\
& \quad+\left\langle\mathbb{1}, \mathrm{P}_{\operatorname{ker} M} z\left(\mu_{2}\right)\right\rangle-\left\langle\mathbb{1}, \mathrm{P}_{\operatorname{ker} M} z\left(\mu_{1}\right)\right\rangle .
\end{aligned}
$$
Now fix a compact set $K$. As $\mu \in K \mapsto \mathrm{P}_{\text {Span } M} z(\mu)$ and $\mu \in K \mapsto\left\langle\mathbb{1}, \mathrm{P}_{\text {ker } M} z(\mu)\right\rangle$ are Lipschitz continuous, there exists a constant $C>0$ such that for all $\mu_{1}, \mu_{2} \in$ $K, \mu_{1} \leqslant \mu_{2}$,
$$
\left\|z\left(\mu_{2}\right)-z\left(\mu_{1}\right)\right\|_{1} \leqslant C\left|\mu_{2}-\mu_{1}\right| .
$$
This shows that $\mu \geqslant 0 \mapsto z(\mu)$ is locally Lipschitz continuous and thus absolutely continuous on compact subsets of $[0,+\infty)$. \(\square\)

\section*{5 The $u \circ v$ case - proof of the results}

The strategy of this section is to reduce the $u \circ v$ case to the $u^{2}$ case. The reduction methods are detailed in Sec. 5.1. In Sec. 5.1.1, we reduce the lasso problem to a positive lasso problem. In Sec. 5.1.2, we reduce the DLN dynamics in the $u \circ v$ case to the dynamics in the $u^{2}$ case. Finally, in Sec. 5.2, we use these elements to deduce Thm. 2.1 from Thm. 3.1 and Thm. 2.2 from Thm. 3.2.

\subsection*{5.1 Reductions}

\subsection*{5.1.1 Reduction of the lasso to the positive lasso}

We study the minimization of the lasso objective:
$$
\min _{\cdot x \in \mathbb{R}^{d}}\left\{\operatorname{Lasso}(x, \mu)=\ell(x)+\left(\lambda+\frac{1}{\mu}\right)\|x\|_{1}\right\}, \quad \ell(x)=\frac{1}{2}\langle x, M x\rangle-\langle r, x\rangle .
$$
We want to connect the lasso minimization problem to a positive lasso minimization problem (3.4). This can be seen as a complexification of the lasso minimization problem, as contrained optimization problems are arguably more delicate to deal with than unconstrained ones. However, the lasso objective is quadratic on nonnegative vectors, while it is not on the full space $\mathbb{R}^{d}$. The constrained minimization of a quadratic has some advantages over the unconstrained minimization of a non-smooth function.

The strategy is to decompose $x$ as the difference $x=y^{\text {pos }}-y^{\text {neg }}$ of two nonnegative vectors $y^{\text {pos }}, y^{\text {neg }} \geqslant 0$. For instance, a canonical choice would be to take $y^{\text {pos }}=x_{+}$and $y^{\text {neg }}=x_{-}$. Note that for such a decomposition,
$$
\ell(x)=\tilde{\ell}(y), \quad y=\binom{y^{\mathrm{pos}}}{y^{\mathrm{neg}}},
$$
where $\widetilde{\ell}$ is the quadratic function
$$
\widetilde{\ell}(y)=\frac{1}{2}\langle y, \widetilde{M} y\rangle-\langle\widetilde{r}, y\rangle, \quad \widetilde{M}=\left(\begin{array}{cc}
M & -M \\
-M & M
\end{array}\right), \quad \widetilde{r}=\binom{r}{-r} .
$$
We define the lasso objective associated to $\widetilde{\ell}$ :
$$
\widetilde{\operatorname{Lasso}}(y, \mu)=\widetilde{\ell}(y)+\left(\lambda+\frac{1}{\mu}\right)\|y\|_{1} .
$$
We denote $\widetilde{\operatorname{PosLasso}}(\mu)=\min _{y \geqslant 0} \widetilde{\operatorname{Lasso}}(y, \mu)$ the minimum of the positive lasso optimization problem associated to $\widetilde{\ell}$.
Lemma 5.1. (1) For any $y=\left(y^{\text {pos }}, y^{\text {neg }}\right) \in \mathbb{R}_{\geqslant 0}^{2 d}$,
$$
\operatorname{Lasso}\left(y^{\text {pos }}-y^{\text {neg }}, \mu\right) \leqslant \widetilde{\operatorname{Lasso}}(y, \mu),
$$
with equality if and only if $\left\langle y^{\text {pos }}, y^{\text {neg }}\right\rangle=0$.
\begin{itemize}
\item[(2)] If $z$ minimizes $\operatorname{Lasso}(., \mu)$ over $\mathbb{R}^{d}$, then $y=\left(z_{+}, z_{-}\right) \in \mathbb{R}_{\geqslant 0}^{2 d}$ minimizes $\widetilde{\operatorname{Lasso}}(., \mu)$ over $\mathbb{R}_{\geqslant 0}^{2 d}$.
\item[(3)] $\operatorname{Lasso}_{*}(\mu)=\overline{\operatorname{PosLasso}}_{*}(\mu)$.
\end{itemize}

Proof. (1) Consider $y=\left(y^{\text {pos }}, y^{\text {neg }}\right) \in \mathbb{R}_{\geqslant 0}^{2 d}$.
$$
\begin{aligned}
\operatorname{Lasso}\left(y^{\operatorname{pos}}-y^{\mathrm{neg}}, \mu\right) & =\ell\left(y^{\mathrm{pos}}-y^{\mathrm{neg}}\right)+\left(\lambda+\frac{1}{\mu}\right)\left\|y^{\mathrm{pos}}-y^{\mathrm{neg}}\right\|_{1} \\
& \leqslant \ell\left(y^{\mathrm{pos}}-y^{\mathrm{neg}}\right)+\left(\lambda+\frac{1}{\mu}\right)\left(\left\|y^{\mathrm{pos}}\right\|_{1}+\left\|y^{\mathrm{neg}}\right\|_{1}\right) \\
& =\widetilde{\ell}(y)+\left(\lambda+\frac{1}{\mu}\right)\|y\|_{1} \\
& =\widetilde{\operatorname{Lasso}}(y, \mu)
\end{aligned}
$$
There is equality if and only if there is equality in the triangle inequality, which happens if and only if $\left\langle y^{\text {pos }}, y^{\text {neg }}\right\rangle=0$.
\begin{itemize}
\item[(2)] Let $z$ be a minimizer of Lasso(., $\mu$ ) over $\mathbb{R}^{d}$. Consider $y=\left(y^{\text {pos }}, y^{\text {neg }}\right) \in$ $\mathbb{R}_{\geqslant 0}^{2 d}$. Then, from (1),
$$
\widetilde{\operatorname{Lasso}}(y, \mu) \geqslant \operatorname{Lasso}\left(y^{\mathrm{pos}}-y^{\mathrm{neg}}, \mu\right) \geqslant \operatorname{Lasso}(z, \mu)=\widetilde{\operatorname{Lasso}}\left(\left(z_{+}, z_{-}\right), \mu\right),
$$
where the equality holds in the last step as $\left\langle z_{+}, z_{-}\right\rangle=0$. As a consequence, $\left(z_{+}, z_{-}\right)$minimizes $\widehat{\operatorname{Lasso}}(., \mu)$ over $\mathbb{R}_{\geqslant 0}^{2 d}$.
\item[(3)] From (1), we have $\operatorname{Lasso}_{*}(\mu) \leqslant \overline{\operatorname{PosLasso}}(\mu)$. Further, if $z$ is a minimizer of $\operatorname{Lasso}(., \mu)$ over $\mathbb{R}^{d}$, then
$$
\operatorname{Lasso}_{*}(\mu)=\operatorname{Lasso}(z, \mu)=\widetilde{\operatorname{Lasso}}\left(\left(z_{+}, z_{-}\right), \mu\right) \geqslant \widehat{\operatorname{PosLasso}}(\mu) .
$$
This proves the equality. \(\square\)
\end{itemize}

\subsection*{5.1.2 Reduction of dynamics in the $u \circ v$ case to the $u \circ u$ case}

Recall that the dynamics in the $u \circ v$ case are defined by
$$
\begin{aligned}
& \frac{\mathrm{d} u}{\mathrm{~d} t}=-\nabla_{u} L(u, v)=-v \circ \nabla \ell(u \circ v)-\lambda u, \\
& \frac{\mathrm{~d} v}{\mathrm{~d} t}=-\nabla_{v} L(u, v)=-u \circ \nabla \ell(u \circ v)-\lambda v .
\end{aligned}
$$
Consider
$$
p^{\text {pos }}=\frac{1}{2}(u+v), \quad \quad p^{\text {neg }}=\frac{1}{2}(u-v) .
$$
Then
$$
u \circ v=\left(p^{\mathrm{pos}}\right)^{2}-\left(p^{\mathrm{neg}}\right)^{2} .
$$
Define $\tilde{t}=\frac{t}{2}$. Then
$$
\begin{aligned}
\frac{\mathrm{d} p^{\mathrm{pos}}}{\mathrm{~d} \tilde{t}} & =\frac{\mathrm{d} t}{\mathrm{~d} \tilde{t}} \frac{1}{2}\left(\frac{\mathrm{~d} u}{\mathrm{~d} t}+\frac{\mathrm{d} v}{\mathrm{~d} t}\right)=\frac{\mathrm{d} u}{\mathrm{~d} t}+\frac{\mathrm{d} v}{\mathrm{~d} t} \\
& =-v \circ \nabla \ell(u \circ v)-u \circ \nabla \ell(u \circ v)-\lambda(u+v) \\
& =-2 p^{\mathrm{pos}} \circ \nabla \ell\left(\left(p^{\mathrm{pos}}\right)^{2}-\left(p^{\mathrm{neg}}\right)^{2}\right)-2 \lambda p^{\mathrm{pos}} \\
& =-2 p^{\mathrm{pos}} \circ \nabla_{y^{\mathrm{pos}}} \widetilde{\ell}\left(\left(p^{\mathrm{pos}}\right)^{2},\left(p^{\mathrm{neg}}\right)^{2}\right)-2 \lambda p^{\mathrm{pos}}
\end{aligned}
$$
Defining
$$
\begin{equation*}
\widetilde{L}\left(p^{\mathrm{pos}}, p^{\mathrm{neg}}\right)=\widetilde{\ell}\left(\left(p^{\mathrm{pos}}\right)^{2},\left(p^{\mathrm{neg}}\right)^{2}\right)+\lambda\left(\left\|p^{\mathrm{pos}}\right\|^{2}+\left\|p^{\mathrm{neg}}\right\|^{2}\right), \tag{5.1}
\end{equation*}
$$
the above equation can be written as
$$
\frac{\mathrm{d} p^{\mathrm{pos}}}{\mathrm{~d} \tilde{t}}=-\nabla_{p^{\mathrm{pos}}} \widetilde{L}\left(p^{\mathrm{pos}}, p^{\mathrm{neg}}\right) .
$$
A similar computation gives that,
$$
\frac{\mathrm{d} p^{\mathrm{neg}}}{\mathrm{~d} \widetilde{t}}=-\nabla_{p^{\mathrm{neg}}} \widetilde{L}\left(p^{\mathrm{pos}}, p^{\mathrm{neg}}\right) .
$$
Thus,
$$
\begin{equation*}
\frac{\mathrm{d}}{\mathrm{~d} \tilde{t}}\left(p^{\text {pos }}, p^{\text {neg }}\right)=-\nabla_{\left(p^{\text {pos }}, p^{\text {neg }}\right)} \widetilde{L}\left(p^{\text {pos }}, p^{\text {neg }}\right) . \tag{5.2}
\end{equation*}
$$
Compare Eqs. (5.1), (5.2) with Eqs. (3.1), (3.2). We have reduced a gradient flow on $L$ in the $u \circ v$ case to a gradient flow on $\widetilde{L}$ in the $u \circ u$ case.

\subsection*{5.2 Proofs}

The proofs of Thms. 2.1 and 2.2 are provided by reductions to Thms. 3.1 and 3.2 respectively.

In each theorem, we are provided a minimizer $x(\mu)$ of $\operatorname{Lasso}(., \mu)$ over $\mathbb{R}^{d}$. By Lemma $5.1(2),\left(x_{+}(\mu), x_{-}(\mu)\right)$ minimizes $\widetilde{\text { Lasso }}(., \mu)$ over $\mathbb{R}_{\geqslant 0}^{2 d}$. This minimizer of the positive lasso will be used in applying Thms 3.1 and 3.2.

Further, we use the reduction of Sec. 5.1.2 from the $u \circ v$ case to the $u^{2}$ case. We keep the same notations in this section, but now denote the dependence in $\varepsilon$ of the solutions. Thus, with $\widetilde{t}=\frac{t}{2}$, we have
$$
\frac{\mathrm{d}}{\mathrm{~d} \tilde{t}}\left(p^{\text {pos }, \varepsilon}, p^{\text {neg }, \varepsilon}\right)=-\nabla_{\left(p^{\text {pos }, \varepsilon}, p^{\text {neg }, \varepsilon}\right)} \widetilde{L}\left(p^{\text {pos }, \varepsilon}, p^{\text {neg }, \varepsilon}\right) .
$$
Again, this is an equation of the form (3.2) in the $u^{2}$ case.
Denote $\left(y^{\mathrm{pos}, \varepsilon}, y^{\mathrm{neg}, \varepsilon}\right)=\left(\left(p^{\mathrm{pos}, \varepsilon}\right)^{2},\left(p^{\mathrm{neg}, \varepsilon}\right)^{2}\right)$ and $\left(\bar{y}^{\mathrm{pos}, \varepsilon}, \bar{y}^{\mathrm{neg}, \varepsilon}\right)$ its timeaverage. The application of Thms. 3.1 and 3.2 decribe the performance of $\left(\bar{y}^{\mathrm{pos}, \varepsilon}, \bar{y}^{\mathrm{neg}, \varepsilon}\right)$ in the minimization of the positive lasso objective $\widetilde{\operatorname{Lasso}}(., \widetilde{s})$, where $\widetilde{s}$ is defined in coherence with Eq. (3.5):
$$
\widetilde{s}=\frac{4}{\log \frac{1}{\varepsilon}} \widetilde{t}=\frac{2}{\log \frac{1}{\varepsilon}} t \underset{(\text { Eq.(2.2)) }}{=} s .
$$
Note that there is a correspondence between the initializations:
$$
\alpha=\left(\frac{1}{2}(\beta+\gamma), \frac{1}{2}(\beta-\gamma)\right) .
$$
As a consequence, the assumption that $\beta_{i} \neq \pm \gamma_{i}, i=1, \ldots, d$, is equivalent to $\alpha_{i} \neq 0, i=1, \ldots, 2 d$.

\subsection*{5.2.1 Proof of Theorem 2.1}

In Thm. 2.1, it is assumed that $\mu \mapsto \mu x(\mu)$ is coordinate-wise monotone. As a consequence, $\mu \mapsto \mu\left(x_{+}(\mu), x_{-}(\mu)\right)$ is coordinate-wise non-decreasing. Thus we can apply Thm. 3.1. We obtain
$$
\widehat{\operatorname{Lasso}}\left(\left(\bar{y}^{\mathrm{pos}, \varepsilon}, \bar{y}^{\mathrm{neg}, \varepsilon}\right), s\right) \underset{\varepsilon \rightarrow 0}{\longrightarrow} \widehat{\operatorname{PosLassO}}_{*}(s) .
$$
We recall from Sec. 5.1.2 that $x^{\varepsilon}=u^{\varepsilon} \circ v^{\varepsilon}=\left(p^{\mathrm{pos}, \varepsilon}\right)^{2}-\left(p^{\mathrm{neg}, \varepsilon}\right)^{2}=y^{\mathrm{pos}, \varepsilon}-y^{\mathrm{neg}, \varepsilon}$. Thus, using Lemma 5.1(1), (3), we obtain
$$
\begin{aligned}
\operatorname{Lasso}\left(\bar{x}^{\varepsilon}(s), s\right)-\operatorname{Lasso}_{*}(s) & =\operatorname{Lasso}\left(\bar{y}^{\mathrm{pos}, \varepsilon}(s)-\bar{y}^{\mathrm{neg}, \varepsilon}(s), s\right)-\operatorname{Lasso}_{*}(s) \\
& \leqslant \widetilde{\operatorname{Lasso}}\left(\left(\bar{y}^{\mathrm{pos}, \varepsilon}, \bar{y}^{\mathrm{neg}, \varepsilon}\right), s\right)-\widetilde{\operatorname{PosLasso}}_{*}(s) \\
& \underset{\varepsilon \rightarrow 0}{\longrightarrow} 0
\end{aligned}
$$

\subsection*{5.2.2 Proof of Theorem 2.2}

In Thm. 2.2, it is assumed that $\mu \mapsto \mu x(\mu)$ is absolutely continuous. As a consequence, $\mu \mapsto \mu\left(x_{+}(\mu), x_{-}(\mu)\right)$ is absolutely continuous. Thus we can apply Thm. 3.2.

Note that the quantity $z^{\downarrow}(\mu)$ defined in Eq. (3.6), when $x(\mu)$ is replaced by $\left(x_{+}(\mu), x_{-}(\mu)\right)$, corresponds to the quantity $z^{\downarrow}(\mu)$ defined in Eq. (2.3). Thus, applying Thm. 3.2, we obtain
$$
\begin{aligned}
& \underset{\varepsilon \rightarrow 0}{\limsup } \widehat{\operatorname{Lasso}}\left(\left(\bar{y}^{\mathrm{pos}, \varepsilon}, \bar{y}^{\mathrm{neg}, \varepsilon}\right), s\right) \\
& \quad \leqslant \widehat{\operatorname{PosLasso}}_{*}(s)+C \eta\left(\lambda, s, z^{\downarrow}(s)\right)
\end{aligned}
$$
Thus, combining with Lemma 5.1(1), (3), we obtain
$$
\begin{aligned}
\underset{\varepsilon \rightarrow 0}{\limsup \operatorname{Lasso}}\left(\bar{x}^{\varepsilon}(s), s\right) & =\underset{\varepsilon \rightarrow 0}{\limsup } \operatorname{Lasso}\left(\bar{y}^{\mathrm{pos}, \varepsilon}(s)-\bar{y}^{\mathrm{neg}, \varepsilon}(s), s\right) \\
& \leqslant \underset{\varepsilon \rightarrow 0}{\limsup } \widetilde{\operatorname{Lasso}}\left(\left(\bar{y}^{\mathrm{pos}, \varepsilon}, \bar{y}^{\mathrm{neg}, \varepsilon}\right), s\right) \\
& \leqslant \widetilde{\operatorname{PosLasso}_{*}}(s)+C \eta\left(\lambda, s, z^{\downarrow}(s)\right) \\
& \leqslant \operatorname{Lasso}_{*}(s)+C \eta\left(\lambda, s, z^{\downarrow}(s)\right)
\end{aligned}
$$

\section*{Acknowledgements}

The author is grateful to Loucas Pillaud-Vivien for numerous stimulating discussions and for providing valuable insights that have improved the development of this work, and to Florent Krzakala for helpful comments. The author also acknowledges support from the ANR and the Ministère de l'Enseignement Supérieur et de la Recherche.

\section*{References}
\begin{itemize}
\item[] [1] Sanjeev Arora, Nadav Cohen, Wei Hu, and Yuping Luo. Implicit regularization in deep matrix factorization. Advances in Neural Information Processing Systems, 2019.
\item[] [2] Shahar Azulay, Edward Moroshko, Mor Shpigel Nacson, Blake Woodworth, Nathan Srebro, Amir Globerson, and Daniel Soudry. On the implicit bias of initialization shape: Beyond infinitesimal mirror descent. In International Conference on Machine Learning, pages 468-477. PMLR, 2021.
\item[] [3] Peter Bartlett, Andrea Montanari, and Alexander Rakhlin. Deep learning: a statistical viewpoint. Acta Numerica, 30:87-201, 2021.
\item[] [4] Raphaël Berthier. Incremental learning in diagonal linear networks. Journal of Machine Learning Research, 24(171):1-26, 2023.
\end{itemize}
[5] Raphaël Berthier. Github repository. https://github.com/ raphael-berthier/dln-lasso, 2025.
[6] Stephen Boyd and Lieven Vandenberghe. Convex Optimization. Cambridge University Press, 2004.
[7] Constantin Carathéodory. Über den variabilitätsbereich der fourier'schen konstanten von positiven harmonischen funktionen. Rendiconti Del Circolo Matematico di Palermo (1884-1940), 32(1):193-217, 1911.
[8] Lenaic Chizat and Francis Bach. Implicit bias of gradient descent for wide two-layer neural networks trained with the logistic loss. In Conference on Learning Theory, pages 1305-1338. PMLR, 2020.
[9] Hung-Hsu Chou, Johannes Maly, and Holger Rauhut. More is less: inducing sparsity via overparameterization. Information and Inference: A Journal of the IMA, 12(3), 2023.
[10] Richard Cottle. Monotone solutions of the parametric linear complementarity problem. Mathematical Programming, 3(1):210-224, 1972.
[11] Richard Cottle. A parametric linear complementarily problem (problem by G. Maier). SIAM Review, 15(2):381-384, 1973.
[12] Richard Cottle, Jong-Shi Pang, and Richard Stone. The linear complementarity problem. SIAM, 2009.
[13] Curtis Eaves. The linear complementarity problem. Management science, 17(9):612-634, 1971.
[14] Bradley Efron, Trevor Hastie, Iain Johnstone, and Robert Tibshirani. Least angle regression. The Annals of Statistics, 32(3):407-499, 2004.
[15] Suriya Gunasekar, Blake Woodworth, Srinadh Bhojanapalli, Behnam Neyshabur, and Nati Srebro. Implicit regularization in matrix factorization. Advances in Neural Information Processing Systems, 2017.
[16] Jeff HaoChen, Colin Wei, Jason Lee, and Tengyu Ma. Shape matters: Understanding the implicit bias of the noise covariance. In Conference on Learning Theory, pages 2315-2357. PMLR, 2021.
[17] Trevor Hastie, Jonathan Taylor, Robert Tibshirani, and Guenther Walther. Forward stagewise regression and the monotone lasso. Electronic Journal of Statistics, 1:1-29, 2007.
[18] Trevor Hastie, Robert Tibshirani, and Martin Wainwright. Statistical learning with sparsity. Monographs on statistics and applied probability, 2015.
[19] Ikuyo Kaneko. A parametric linear complementarity problem involving derivatives. Mathematical programming, 15(1):146-154, 1978.
[20] Jiangyuan Li, Thanh Nguyen, Chinmay Hegde, and Ka Wai Wong. Implicit sparse regularization: The impact of depth and early stopping. Advances in Neural Information Processing Systems, 2021.
[21] Yuanzhi Li, Tengyu Ma, and Hongyang Zhang. Algorithmic regularization in over-parameterized matrix sensing and neural networks with quadratic activations. In Conference on Learning Theory, pages 2-47. PMLR, 2018.
[22] Zhiyuan Li, Yuping Luo, and Kaifeng Lyu. Towards resolving the implicit bias of gradient descent for matrix factorization: Greedy low-rank learning. Internation Conference on Learning Representations, 2021.
[23] Zhiyuan Li, Tianhao Wang, Jason Lee, and Sanjeev Arora. Implicit bias of gradient descent on reparametrized models: On equivalence to mirror descent. Advances in Neural Information Processing Systems, 2022.
[24] Nimrod Megiddo. On monotonicity in parametric linear complementarity problems. Mathematical Programming, 12:60-66, 1977.
[25] Mor Shpigel Nacson, Kavya Ravichandran, Nathan Srebro, and Daniel Soudry. Implicit bias of the step size in linear diagonal neural networks. In International Conference on Machine Learning, pages 16270-16295. PMLR, 2022.
[26] Scott Pesme and Nicolas Flammarion. Saddle-to-saddle dynamics in diagonal linear networks. Advances in Neural Information Processing Systems, 2023.
[27] Scott Pesme, Loucas Pillaud-Vivien, and Nicolas Flammarion. Implicit bias of SGD for diagonal linear networks: a provable benefit of stochasticity. Advances in Neural Information Processing Systems, 2021.
[28] Loucas Pillaud-Vivien, Julien Reygner, and Nicolas Flammarion. Label noise (stochastic) gradient descent implicitly solves the Lasso for quadratic parametrisation. In Conference on Learning Theory, pages 2127-2159. PMLR, 2022.
[29] Saharon Rosset, Ji Zhu, and Trevor Hastie. Boosting as a regularized path to a maximum margin classifier. Journal of Machine Learning Research, 5(Aug):941-973, 2004.
[30] Ryan Tibshirani. The lasso problem and uniqueness. Electronic Journal of Statistics, 7:1456-1490, 2013.
[31] Ryan Tibshirani. Equivalences between sparse models and neural networks. https://www.stat.berkeley.edu/~ryantibs/papers/ sparsitynn.pdf, 2021.
[32] Gal Vardi. On the implicit bias in deep-learning algorithms. Communications of the ACM, 66(6):86-93, 2023.
\begin{itemize}
\item[] [33] Tomas Vaskevicius, Varun Kanade, and Patrick Rebeschini. Implicit regularization for optimal sparse recovery. Advances in Neural Information Processing Systems, 2019.
\item[] [34] Blake Woodworth, Suriya Gunasekar, Jason Lee, Edward Moroshko, Pedro Savarese, Itay Golan, Daniel Soudry, and Nathan Srebro. Kernel and rich regimes in overparametrized models. In Conference on Learning Theory, pages 3635-3673. PMLR, 2020.
\item[] [35] Peng Zhao, Yun Yang, and Qiao-Chu He. High-dimensional linear regression via implicit regularization. Biometrika, 109(4):1033-1046, 2022.
\end{itemize}