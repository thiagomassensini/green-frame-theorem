# Teorema — Carta Bracketada Adaptada a Caracteres de Dirichlet

## Diferenças finitas sincronizadas, núcleo dilatado, continuação holomorfa e preservação de zeros

> [!IMPORTANT]
> **Status documental:** `RESEARCH_INPUT_UNFORMALIZED`
>
> Este arquivo é uma fonte matemática de pesquisa. Ele **não pertence ao `ACTIVE_CORE`** da rota vigente e não foi promovido a endpoint Lean vigente.
>
> Declarações obrigatórias:
> - Esta construção **não deve ser confundida** com a carta saturada trivial $p=5$ da spine atual, cujo fingerprint é $F_2\Phi_5 = F_5 P$.
> - A possível carta sincronizada com o caráter principal módulo 2 permanece como `PROMISING_RESERVE`, conforme o cânone.
> - Nenhuma conclusão global deve ser transportada para a rota atual sem formalização completa e auditoria de dependências.
>
> A validade matemática interna do documento não está em questão. O que está separado é o seu **estatuto formal no projeto**: reserva de pesquisa, não endpoint ativo.
> Consulte [`CANON_ROTA_VIGENTE_MIDDLE_GENUINE_C2.md`](./CANON_ROTA_VIGENTE_MIDDLE_GENUINE_C2.md), seções 6.18 e checkpoint vigente.

> Documento matemático autônomo, formal e GitHub Friendly.
>
> O desenvolvimento utiliza apenas:
>
> - periodicidade de caracteres de Dirichlet;
> - multiplicatividade;
> - aritmética modular;
> - diferenças finitas centradas;
> - Teorema Fundamental do Cálculo;
> - convergência normal de séries holomorfas.
>
> Nenhuma formulação em teoria das distribuições é necessária.

---

## Sumário

1. [Objetivo](#1-objetivo)
2. [Hipóteses e notação](#2-hipóteses-e-notação)
3. [Por que o bracket de passo comum pode falhar](#3-por-que-o-bracket-de-passo-comum-pode-falhar)
4. [Bracket sincronizado com o período](#4-bracket-sincronizado-com-o-período)
5. [Fatoração exata do caráter](#5-fatoração-exata-do-caráter)
6. [Núcleo dilatado $K_{p,q}$](#6-núcleo-dilatado-k_pq)
7. [Representação integral](#7-representação-integral)
8. [Massa do núcleo](#8-massa-do-núcleo)
9. [Ganho recuperado de duas potências](#9-ganho-recuperado-de-duas-potências)
10. [Convergência absoluta e normal](#10-convergência-absoluta-e-normal)
11. [Termos de fronteira](#11-termos-de-fronteira)
12. [Lema de reindexação modular](#12-lema-de-reindexação-modular)
13. [Carta bracketada adaptada](#13-carta-bracketada-adaptada)
14. [Teorema principal](#14-teorema-principal)
15. [Prova do teorema principal](#15-prova-do-teorema-principal)
16. [Continuação da função $L$](#16-continuação-da-função-l)
17. [Preservação dos zeros no critical strip](#17-preservação-dos-zeros-no-critical-strip)
18. [Preservação de multiplicidades](#18-preservação-de-multiplicidades)
19. [Atlas entre diferentes primos](#19-atlas-entre-diferentes-primos)
20. [Exemplo $p=5$, $q=3$, $\chi=\chi_3$](#20-exemplo-p5-q3-chichi_3)
21. [Assíntota do bracket comum no exemplo](#21-assíntota-do-bracket-comum-no-exemplo)
22. [Assíntota do bracket sincronizado no exemplo](#22-assíntota-do-bracket-sincronizado-no-exemplo)
23. [Verificação numérica ilustrativa](#23-verificação-numérica-ilustrativa)
24. [Escopo e limitações](#24-escopo-e-limitações)
25. [Corolários consolidados](#25-corolários-consolidados)
26. [Rota sugerida para formalização em Lean 4](#26-rota-sugerida-para-formalização-em-lean-4)
27. [Síntese final](#27-síntese-final)

---

# 1. Objetivo

Considere uma função $L$ de Dirichlet

$$
L(s,\chi)
=
\sum_{n=1}^{\infty}\chi(n)n^{-s},
\qquad
\Re(s)>1,
$$

associada a um caráter de Dirichlet $\chi$ de módulo $q$.

O objetivo é construir uma série bracketada que:

1. sincronize a diferença finita com o período $q$;
2. recupere o ganho de duas potências de decaimento;
3. convirja absoluta e localmente uniformemente em
   $$
   \Re(s)>-1;
   $$
4. coincida, na região original $\Re(s)>1$, com
   $$
   \left(1-\chi(p)p^{1-s}\right)L(s,\chi);
   $$
5. preserve exatamente os zeros de $L(s,\chi)$ no interior do critical strip.

A construção depende de um primo ímpar $p$ satisfazendo

$$
\gcd(p,q)=1.
$$

---

# 2. Hipóteses e notação

Fixe:

- um inteiro
  $$
  q\geq2;
  $$
- um caráter de Dirichlet módulo $q$,
  $$
  \chi:\mathbb Z\to\mathbb C;
  $$
- um primo ímpar $p$ com
  $$
  \gcd(p,q)=1;
  $$
- o semialcance
  $$
  \boxed{
  h=\frac{p-1}{2};
  }
  $$
- um parâmetro complexo
  $$
  s=\sigma+it.
  $$

O caráter satisfaz:

$$
\chi(n+q)=\chi(n),
$$

$$
\chi(mn)=\chi(m)\chi(n),
$$

$$
\chi(n)=0
\quad\Longleftrightarrow\quad
\gcd(n,q)>1,
$$

e, quando $\gcd(n,q)=1$,

$$
|\chi(n)|=1.
$$

Como $\gcd(p,q)=1$,

$$
\boxed{
|\chi(p)|=1.
}
$$

Defina, para $n\in\mathbb Z$,

$$
\boxed{
a_s(n)
=
\begin{cases}
\chi(n)n^{-s}, & n\geq1,\$$4pt]
0, & n\leq0.
\end{cases}
}
$$

A extensão por zero evita ambiguidades nos poucos centros próximos da fronteira $n=0$.

---

# 3. Por que o bracket de passo comum pode falhar

Considere o bracket não adaptado:

$$
B_{p,\chi,m}^{\mathrm{std}}(s)
=
\sum_{j=1}^{h}
\left[
a_s(pm-j)
-2a_s(pm)
+a_s(pm+j)
\right].
$$

Para $m$ grande,

$$
(pm\pm j)^{-s}
=
(pm)^{-s}
+
O_s\left(m^{-\sigma-1}\right).
$$

Logo,

$$
\boxed{
\begin{aligned}
B_{p,\chi,m}^{\mathrm{std}}(s)
={}&
(pm)^{-s}
\sum_{j=1}^{h}
\Big[
\chi(pm-j)
-2\chi(pm)
+\chi(pm+j)
\Big]
\\
&+
O_{p,s}\left(m^{-\sigma-1}\right).
\end{aligned}
}
$$

Defina o coeficiente discreto do caráter:

$$
\boxed{
C_{p,\chi}(m)
=
\sum_{j=1}^{h}
\Big[
\chi(pm-j)
-2\chi(pm)
+\chi(pm+j)
\Big].
}
$$

Se

$$
C_{p,\chi}(m)\neq0
$$

ao longo de uma classe residual recorrente, então o termo dominante é

$$
(pm)^{-s}C_{p,\chi}(m).
$$

Consequentemente,

$$
\boxed{
B_{p,\chi,m}^{\mathrm{std}}(s)
=
O\left(m^{-\sigma}\right),
}
$$

e não

$$
O\left(m^{-\sigma-2}\right).
$$

Portanto, o bracket comum pode medir principalmente a oscilação discreta de $\chi$, em vez da curvatura de $n^{-s}$.

---

# 4. Bracket sincronizado com o período

Para sincronizar a diferença finita com o período $q$, substitua o passo $j$ pelo passo

$$
qj.
$$

Defina o bracket adaptado no centro $pm$:

$$
\boxed{
\mathfrak b_{p,q,\chi,m}(s)
=
\sum_{j=1}^{h}
\left[
a_s(pm-qj)
-2a_s(pm)
+a_s(pm+qj)
\right].
}
$$

Para centros suficientemente grandes, isto é, quando

$$
pm>qh,
$$

todos os argumentos são positivos e a extensão por zero deixa de participar.

---

# 5. Fatoração exata do caráter

Como $qj$ é múltiplo do período $q$,

$$
\chi(pm-qj)
=
\chi(pm)
=
\chi(pm+qj).
$$

Portanto, para

$$
pm>qh,
$$

temos

$$
\boxed{
\begin{aligned}
\mathfrak b_{p,q,\chi,m}(s)
=
\chi(pm)
\sum_{j=1}^{h}
\Big[
&(pm-qj)^{-s}
\\
&-2(pm)^{-s}
\\
&+(pm+qj)^{-s}
\Big].
\end{aligned}
}
$$

Usando a multiplicatividade,

$$
\chi(pm)
=
\chi(p)\chi(m).
$$

Logo,

$$
\boxed{
\mathfrak b_{p,q,\chi,m}(s)
=
\chi(p)\chi(m)\,
B_{pm,q}^{(p)}(s),
}
$$

onde

$$
\boxed{
B_{c,q}^{(p)}(s)
=
\sum_{j=1}^{h}
\left[
(c-qj)^{-s}
-2c^{-s}
+(c+qj)^{-s}
\right].
}
$$

O caráter foi completamente isolado para fora da diferença finita.

---

# 6. Núcleo dilatado $K_{p,q}$

Para o bracket original de raios $j$, o núcleo triangular é

$$
(j-|u|)_+.
$$

Para o passo $qj$, o núcleo correspondente é

$$
(qj-|u|)_+.
$$

Defina

$$
\boxed{
K_{p,q}(u)
=
\sum_{j=1}^{h}
(qj-|u|)_+.
}
$$

Se

$$
K_p(v)
=
\sum_{j=1}^{h}
(j-|v|)_+,
$$

então

$$
\boxed{
K_{p,q}(u)
=
qK_p\left(\frac{u}{q}\right).
}
$$

Portanto, $K_{p,q}$ é a dilatação horizontal do núcleo $K_p$ por um fator $q$, acompanhada da dilatação vertical necessária para preservar a forma triangular.

O suporte é

$$
\boxed{
\operatorname{supp}(K_{p,q})
\subseteq[-qh,qh].
}
$$

Além disso,

$$
K_{p,q}(u)\geq0
$$

e

$$
K_{p,q}(-u)=K_{p,q}(u).
$$

---

# 7. Representação integral

Para uma função $f\in C^2$, a segunda diferença de passo $qj$ satisfaz

$$
\boxed{
f(c-qj)-2f(c)+f(c+qj)
=
\int_{-qj}^{qj}
(qj-|u|)f''(c+u)\,du.
}
$$

Somando em $j$,

$$
\boxed{
B_{c,q}^{(p)}[f]
=
\int_{-qh}^{qh}
K_{p,q}(u)f''(c+u)\,du.
}
$$

Para

$$
f_s(x)=x^{-s},
$$

temos

$$
f_s''(x)
=
s(s+1)x^{-s-2}.
$$

Logo,

$$
\boxed{
B_{c,q}^{(p)}(s)
=
s(s+1)
\int_{-qh}^{qh}
K_{p,q}(u)
(c+u)^{-s-2}\,du.
}
$$

Consequentemente, para $pm>qh$,

$$
\boxed{
\begin{aligned}
\mathfrak b_{p,q,\chi,m}(s)
={}&
\chi(pm)s(s+1)
\\
&\times
\int_{-qh}^{qh}
K_{p,q}(u)
(pm+u)^{-s-2}\,du.
\end{aligned}
}
$$

Essa identidade é exata.

---

# 8. Massa do núcleo

Para cada raio $qj$,

$$
\int_{-qj}^{qj}
(qj-|u|)\,du
=
(qj)^2.
$$

Portanto,

$$
\begin{aligned}
\int_{-qh}^{qh}
K_{p,q}(u)\,du
&=
\sum_{j=1}^{h}(qj)^2
\\
&=
q^2\sum_{j=1}^{h}j^2.
\end{aligned}
$$

Como

$$
\sum_{j=1}^{h}j^2
=
\frac{p(p^2-1)}{24},
$$

obtemos

$$
\boxed{
\int_{-qh}^{qh}
K_{p,q}(u)\,du
=
q^2
\frac{p(p^2-1)}{24}.
}
$$

A dilatação do passo multiplica a massa do núcleo por

$$
q^2.
$$

---

# 9. Ganho recuperado de duas potências

Fixe um compacto

$$
\mathcal K
\subset
\{s\in\mathbb C:\Re(s)>-1\}.
$$

Defina

$$
\sigma_0
=
\inf_{s\in\mathcal K}\Re(s)>-1.
$$

Para $m$ suficientemente grande,

$$
pm-qh
\geq
\frac{p}{2}m.
$$

Usando a representação integral,

$$
\begin{aligned}
\left|
\mathfrak b_{p,q,\chi,m}(s)
\right|
&\leq
|s(s+1)|
\int_{-qh}^{qh}
K_{p,q}(u)
(pm+u)^{-\sigma-2}\,du.
\end{aligned}
$$

Como

$$
|\chi(pm)|\leq1
$$

e

$$
pm+u\geq pm-qh,
$$

segue que

$$
\left|
\mathfrak b_{p,q,\chi,m}(s)
\right|
\leq
|s(s+1)|
\left(
\int K_{p,q}
\right)
(pm-qh)^{-\sigma-2}.
$$

Uniformemente em $s\in\mathcal K$,

$$
\boxed{
\left|
\mathfrak b_{p,q,\chi,m}(s)
\right|
\leq
C_{\mathcal K,p,q}
m^{-\sigma_0-2}.
}
$$

Assim,

$$
\boxed{
\mathfrak b_{p,q,\chi,m}(s)
=
O_{\mathcal K,p,q}
\left(
m^{-\sigma_0-2}
\right).
}
$$

O ganho de duas potências foi recuperado.

## 9.1 Termo assintótico principal

Para $m\to\infty$,

$$
\boxed{
\begin{aligned}
\mathfrak b_{p,q,\chi,m}(s)
={}&
\chi(pm)
q^2
\left(
\sum_{j=1}^{h}j^2
\right)
s(s+1)
(pm)^{-s-2}
\\
&+
O_{p,q,s}
\left(
m^{-\sigma-4}
\right).
\end{aligned}
}
$$

Equivalentemente,

$$
\boxed{
\begin{aligned}
\mathfrak b_{p,q,\chi,m}(s)
={}&
\chi(pm)
q^2
\frac{p(p^2-1)}{24}
s(s+1)
(pm)^{-s-2}
\\
&+
O_{p,q,s}
\left(
m^{-\sigma-4}
\right).
\end{aligned}
}
$$

---

# 10. Convergência absoluta e normal

Defina a série bracketada adaptada:

$$
\boxed{
\mathcal B_{p,q,\chi}(s)
=
\sum_{m=1}^{\infty}
\mathfrak b_{p,q,\chi,m}(s).
}
$$

Os termos com

$$
pm\leq qh
$$

são finitos em número e não afetam a convergência.

Para o restante, em qualquer compacto

$$
\mathcal K
\subset
\{\Re(s)>-1\},
$$

temos

$$
\left|
\mathfrak b_{p,q,\chi,m}(s)
\right|
\leq
C_{\mathcal K,p,q}
m^{-\sigma_0-2},
$$

com

$$
\sigma_0>-1.
$$

Como

$$
\sigma_0+2>1,
$$

a série majorante

$$
\sum_{m=1}^{\infty}
m^{-\sigma_0-2}
$$

converge.

Pelo teste de Weierstrass,

$$
\boxed{
\mathcal B_{p,q,\chi}(s)
\text{ converge absoluta e localmente uniformemente em }
\Re(s)>-1.
}
$$

Cada termo é uma função inteira de $s$.

Logo,

$$
\boxed{
\mathcal B_{p,q,\chi}
\text{ é holomorfa em }
\Re(s)>-1.
}
$$

---

# 11. Termos de fronteira

Os laterais

$$
pm+qj
$$

sempre são positivos.

Já os termos

$$
pm-qj
$$

podem ser não positivos para os primeiros valores de $m$.

Além disso, alguns inteiros positivos não divisíveis por $p$ aparecem na classe residual $+qj\pmod p$, mas corresponderiam a um índice $m\leq0$ na expressão

$$
pm+qj.
$$

Esses termos formam uma correção finita.

Defina

$$
\boxed{
\mathcal C_{p,q}
=
\left\{
qj-rp>0:
1\leq j\leq h,
\;
r\in\mathbb Z_{\geq0}
\right\}.
}
$$

O conjunto é finito, pois

$$
qj-rp>0
$$

implica

$$
0\leq r<\frac{qj}{p}
\leq
\frac{qh}{p}.
$$

## 11.1 Unicidade

Se

$$
qj-rp
=
qj'-r'p,
$$

então

$$
q(j-j')
=
p(r-r').
$$

Como

$$
\gcd(p,q)=1,
$$

temos

$$
p\mid(j-j').
$$

Mas

$$
|j-j'|<p.
$$

Logo,

$$
j=j'
$$

e, em seguida,

$$
r=r'.
$$

Portanto, cada elemento da correção possui representação única.

Defina a função inteira de correção:

$$
\boxed{
E_{p,q,\chi}(s)
=
\sum_{n\in\mathcal C_{p,q}}
\chi(n)n^{-s}.
}
$$

---

# 12. Lema de reindexação modular

## Lema

Seja

$$
\mathcal L_{p,q}
=
\left\{
pm-qj>0,\;
pm+qj:
m\geq1,\;
1\leq j\leq h
\right\}.
$$

Então, sem multiplicidades,

$$
\boxed{
\mathcal L_{p,q}
=
\left\{
n\geq1:
p\nmid n
\right\}
\setminus
\mathcal C_{p,q}.
}
$$

## Prova

Os resíduos

$$
\pm qj
\pmod p,
\qquad
1\leq j\leq h,
$$

percorrem todos os resíduos não nulos módulo $p$.

De fato, os resíduos

$$
\pm j,
\qquad
1\leq j\leq h,
$$

já percorrem todos os resíduos não nulos módulo $p$, e a multiplicação por $q$ é uma permutação módulo $p$, pois

$$
\gcd(p,q)=1.
$$

Logo, para cada inteiro positivo $n$ com $p\nmid n$, existem únicos:

- $j\in\{1,\ldots,h\}$;
- sinal $\varepsilon\in\{-1,+1\}$;

tais que

$$
n\equiv\varepsilon qj\pmod p.
$$

Se

$$
\varepsilon=-1,
$$

então

$$
n=pm-qj
$$

com

$$
m=\frac{n+qj}{p}\geq1.
$$

Se

$$
\varepsilon=+1,
$$

então

$$
n=pm+qj
$$

para algum inteiro $m$.

Quando $m\geq1$, o termo pertence a $\mathcal L_{p,q}$.

Quando $m\leq0$, escrevendo

$$
m=-r,
\qquad
r\geq0,
$$

temos

$$
n=qj-rp>0,
$$

isto é,

$$
n\in\mathcal C_{p,q}.
$$

A unicidade dos resíduos garante ausência de duplicações.

Conclui-se o lema. $\square$

---

# 13. Carta bracketada adaptada

Defina a carta:

$$
\boxed{
\Phi_{p,q,\chi}(s)
=
E_{p,q,\chi}(s)
+
\mathcal B_{p,q,\chi}(s).
}
$$

Explicitamente,

$$
\boxed{
\begin{aligned}
\Phi_{p,q,\chi}(s)
={}&
\sum_{n\in\mathcal C_{p,q}}
\chi(n)n^{-s}
\\
&+
\sum_{m=1}^{\infty}
\sum_{j=1}^{h}
\Big[
a_s(pm-qj)
\\
&\qquad
-2a_s(pm)
+
a_s(pm+qj)
\Big].
\end{aligned}
}
$$

A função $\Phi_{p,q,\chi}$ é holomorfa em

$$
\Re(s)>-1.
$$

---

# 14. Teorema principal

## Teorema — Carta Bracketada Adaptada a Caracteres de Dirichlet

Seja $\chi$ um caráter de Dirichlet módulo $q$, e seja $p$ um primo ímpar com

$$
\gcd(p,q)=1.
$$

Defina

$$
h=\frac{p-1}{2},
$$

o bracket adaptado

$$
\mathfrak b_{p,q,\chi,m}(s)
=
\sum_{j=1}^{h}
\left[
a_s(pm-qj)
-2a_s(pm)
+a_s(pm+qj)
\right],
$$

a correção finita

$$
E_{p,q,\chi}(s)
=
\sum_{n\in\mathcal C_{p,q}}
\chi(n)n^{-s},
$$

e a carta

$$
\Phi_{p,q,\chi}(s)
=
E_{p,q,\chi}(s)
+
\sum_{m=1}^{\infty}
\mathfrak b_{p,q,\chi,m}(s).
$$

Então:

### 1. Representação integral da cauda

Para todo $m$ tal que

$$
pm>qh,
$$

vale

$$
\boxed{
\begin{aligned}
\mathfrak b_{p,q,\chi,m}(s)
={}&
\chi(pm)s(s+1)
\\
&\times
\int_{-qh}^{qh}
K_{p,q}(u)
(pm+u)^{-s-2}\,du.
\end{aligned}
}
$$

### 2. Convergência normal

A série que define $\Phi_{p,q,\chi}$ converge absoluta e localmente uniformemente em

$$
\boxed{
\Re(s)>-1.
}
$$

Consequentemente,

$$
\boxed{
\Phi_{p,q,\chi}
\text{ é holomorfa em }
\Re(s)>-1.
}
$$

### 3. Identidade global

Na região

$$
\Re(s)>1,
$$

vale

$$
\boxed{
\Phi_{p,q,\chi}(s)
=
\left(
1-\chi(p)p^{1-s}
\right)
L(s,\chi).
}
$$

### 4. Carta de continuação

Nos pontos de

$$
\Re(s)>-1
$$

em que

$$
1-\chi(p)p^{1-s}\neq0,
$$

a função

$$
\boxed{
L_{p,q,\chi}^{\mathrm{br}}(s)
=
\frac{
\Phi_{p,q,\chi}(s)
}{
1-\chi(p)p^{1-s}
}
}
$$

é uma continuação holomorfa da série de Dirichlet $L(s,\chi)$.

### 5. Equivalência de zeros

No interior do critical strip,

$$
0<\Re(s)<1,
$$

vale

$$
\boxed{
\Phi_{p,q,\chi}(s)=0
\iff
L_{p,q,\chi}^{\mathrm{br}}(s)=0.
}
$$

As multiplicidades são preservadas.

---

# 15. Prova do teorema principal

## 15.1 Representação integral

Para $pm>qh$, todos os argumentos são positivos.

Pela periodicidade,

$$
\chi(pm\pm qj)=\chi(pm).
$$

Logo,

$$
\mathfrak b_{p,q,\chi,m}(s)
=
\chi(pm)
\sum_{j=1}^{h}
\left[
(pm-qj)^{-s}
-2(pm)^{-s}
+(pm+qj)^{-s}
\right].
$$

A representação integral das segundas diferenças fornece

$$
\mathfrak b_{p,q,\chi,m}(s)
=
\chi(pm)s(s+1)
\int_{-qh}^{qh}
K_{p,q}(u)
(pm+u)^{-s-2}\,du.
$$

## 15.2 Convergência normal

Em qualquer compacto

$$
\mathcal K\subset\{\Re(s)>-1\},
$$

a representação integral fornece

$$
\left|
\mathfrak b_{p,q,\chi,m}(s)
\right|
\leq
C_{\mathcal K,p,q}
m^{-\sigma_0-2},
$$

onde

$$
\sigma_0
=
\inf_{s\in\mathcal K}\Re(s)>-1.
$$

Como

$$
\sum m^{-\sigma_0-2}
$$

converge, a série é normalmente convergente.

## 15.3 Soma lateral

Pelo lema de reindexação, para $\Re(s)>1$,

$$
\begin{aligned}
&
E_{p,q,\chi}(s)
\\
&+
\sum_{m=1}^{\infty}
\sum_{j=1}^{h}
\left[
a_s(pm-qj)
+a_s(pm+qj)
\right]
\\
&=
\sum_{\substack{n\geq1\\p\nmid n}}
\chi(n)n^{-s}.
\end{aligned}
$$

Como $\chi$ é multiplicativa e $\gcd(p,q)=1$,

$$
\sum_{\substack{n\geq1\\p\nmid n}}
\chi(n)n^{-s}
=
\left(
1-\chi(p)p^{-s}
\right)L(s,\chi).
$$

## 15.4 Soma central

Existem

$$
2h=p-1
$$

cópias do centro.

Portanto,

$$
\begin{aligned}
2h
\sum_{m=1}^{\infty}
\chi(pm)(pm)^{-s}
&=
(p-1)
\chi(p)p^{-s}
L(s,\chi).
\end{aligned}
$$

## 15.5 Subtração

Assim,

$$
\begin{aligned}
\Phi_{p,q,\chi}(s)
={}&
\left(
1-\chi(p)p^{-s}
\right)L(s,\chi)
\\
&-
(p-1)\chi(p)p^{-s}L(s,\chi)
\\
={}&
\left[
1-p\chi(p)p^{-s}
\right]L(s,\chi)
\\
={}&
\left[
1-\chi(p)p^{1-s}
\right]L(s,\chi).
\end{aligned}
$$

Isso prova a identidade global em $\Re(s)>1$.

## 15.6 Continuação

Como $\Phi_{p,q,\chi}$ é holomorfa em $\Re(s)>-1$, o quociente

$$
\frac{
\Phi_{p,q,\chi}(s)
}{
1-\chi(p)p^{1-s}
}
$$

é holomorfo onde o denominador não zera.

Na região $\Re(s)>1$, ele coincide com a série de Dirichlet original.

Logo, fornece sua continuação.

$\square$

---

# 16. Continuação da função $L$

Defina o fator da carta:

$$
\boxed{
G_{p,\chi}(s)
=
1-\chi(p)p^{1-s}.
}
$$

A carta satisfaz

$$
\Phi_{p,q,\chi}
=
G_{p,\chi}
L
$$

na região original de convergência.

Portanto,

$$
\boxed{
L_{p,q,\chi}^{\mathrm{br}}(s)
=
\frac{
\Phi_{p,q,\chi}(s)
}{
G_{p,\chi}(s)
}
}
$$

é uma continuação da função $L$ em toda região onde

$$
G_{p,\chi}(s)\neq0.
$$

## 16.1 Caráter não principal

Se $\chi$ é não principal, a função $L(s,\chi)$ possui continuação inteira na teoria clássica.

A carta bracketada coincide com essa continuação por unicidade analítica.

## 16.2 Caráter principal

Se $\chi$ é principal, a função $L(s,\chi)$ possui um polo em $s=1$.

A carta $\Phi_{p,q,\chi}$ permanece holomorfa; o polo reaparece ao dividir pelo zero de $G_{p,\chi}$ em $s=1$.

---

# 17. Preservação dos zeros no critical strip

Como

$$
\gcd(p,q)=1,
$$

temos

$$
|\chi(p)|=1.
$$

Se

$$
0<\sigma<1,
$$

então

$$
\left|
\chi(p)p^{1-s}
\right|
=
p^{1-\sigma}
>
1.
$$

Logo,

$$
\chi(p)p^{1-s}\neq1.
$$

Portanto,

$$
\boxed{
G_{p,\chi}(s)\neq0
\qquad
\text{para }
0<\Re(s)<1.
}
$$

Assim,

$$
\boxed{
\Phi_{p,q,\chi}(s)=0
\iff
L_{p,q,\chi}^{\mathrm{br}}(s)=0
}
$$

em todo o interior do critical strip.

A carta não introduz zeros artificiais nessa região.

---

# 18. Preservação de multiplicidades

Seja $\rho$ um zero de $L_{p,q,\chi}^{\mathrm{br}}$ no critical strip.

Como

$$
G_{p,\chi}(\rho)\neq0,
$$

existe uma vizinhança de $\rho$ na qual $G_{p,\chi}$ é uma unidade holomorfa.

Se

$$
L_{p,q,\chi}^{\mathrm{br}}(s)
=
(s-\rho)^mH(s),
$$

com

$$
H(\rho)\neq0,
$$

então

$$
\Phi_{p,q,\chi}(s)
=
(s-\rho)^m
G_{p,\chi}(s)
H(s).
$$

Como

$$
G_{p,\chi}(\rho)H(\rho)\neq0,
$$

a ordem do zero permanece $m$.

Portanto,

$$
\boxed{
\operatorname{ord}_\rho
\Phi_{p,q,\chi}
=
\operatorname{ord}_\rho
L_{p,q,\chi}^{\mathrm{br}}.
}
$$

---

# 19. Atlas entre diferentes primos

Sejam $p$ e $r$ primos ímpares, ambos coprimos a $q$.

As cartas satisfazem

$$
\Phi_{p,q,\chi}
=
G_{p,\chi}L
$$

e

$$
\Phi_{r,q,\chi}
=
G_{r,\chi}L.
$$

Logo,

$$
\boxed{
G_{r,\chi}(s)
\Phi_{p,q,\chi}(s)
=
G_{p,\chi}(s)
\Phi_{r,q,\chi}(s).
}
$$

Essa é a lei de colagem do atlas.

## 19.1 Zeros do fator da carta

Se

$$
\chi(p)=e^{i\theta_p},
$$

então

$$
G_{p,\chi}(s)=0
$$

se, e somente se,

$$
e^{i\theta_p}p^{1-s}=1.
$$

Logo, todos os zeros de $G_{p,\chi}$ estão sobre

$$
\boxed{
\Re(s)=1.
}
$$

Assim, no interior do critical strip, nenhuma carta precisa ser trocada por causa do fator.

Fora dessa região, cartas associadas a diferentes primos podem ser usadas como patches complementares.

---

# 20. Exemplo $p=5$, $q=3$, $\chi=\chi_3$

Considere o caráter real módulo $3$:

$$
\chi_3(n)
=
\begin{cases}
0, & 3\mid n,\$$4pt]
1, & n\equiv1\pmod3,\$$4pt]
-1, & n\equiv2\pmod3.
\end{cases}
$$

Escolha

$$
p=5,
\qquad
q=3,
\qquad
h=2.
$$

O bracket adaptado é

$$
\boxed{
\begin{aligned}
\mathfrak b_{5,3,\chi_3,m}(s)
={}&
a_s(5m-3)
-2a_s(5m)
+a_s(5m+3)
\\
&+
a_s(5m-6)
-2a_s(5m)
+a_s(5m+6).
\end{aligned}
}
$$

## 20.1 Correção finita

O conjunto de correção é

$$
\mathcal C_{5,3}
=
\left\{
3j-5r>0:
j\in\{1,2\},
\;
r\geq0
\right\}.
$$

Para $j=1$:

$$
3-5r>0
$$

fornece apenas

$$
3.
$$

Para $j=2$:

$$
6-5r>0
$$

fornece

$$
6
\quad\text{e}\quad
1.
$$

Logo,

$$
\boxed{
\mathcal C_{5,3}
=
\{1,3,6\}.
}
$$

Como

$$
\chi_3(1)=1,
\qquad
\chi_3(3)=0,
\qquad
\chi_3(6)=0,
$$

temos

$$
\boxed{
E_{5,3,\chi_3}(s)=1.
}
$$

## 20.2 Fator da carta

Como

$$
5\equiv2\pmod3,
$$

temos

$$
\chi_3(5)=-1.
$$

Logo,

$$
G_{5,\chi_3}(s)
=
1-\chi_3(5)5^{1-s}
=
1+5^{1-s}.
$$

A identidade global é

$$
\boxed{
1
+
\sum_{m=1}^{\infty}
\mathfrak b_{5,3,\chi_3,m}(s)
=
\left(
1+5^{1-s}
\right)
L(s,\chi_3).
}
$$

---

# 21. Assíntota do bracket comum no exemplo

Considere valores de $m$ satisfazendo

$$
m\equiv1\pmod3.
$$

Então

$$
5m\equiv2\pmod3,
$$

e

$$
\chi_3(5m)=-1.
$$

Para $j=1$,

$$
\chi_3(5m-1)
-2\chi_3(5m)
+\chi_3(5m+1)
=
1-2(-1)+0
=
3.
$$

Para $j=2$,

$$
\chi_3(5m-2)
-2\chi_3(5m)
+\chi_3(5m+2)
=
0-2(-1)+1
=
3.
$$

Somando,

$$
\boxed{
C_{5,\chi_3}(m)=6.
}
$$

Logo,

$$
\boxed{
B_{5,\chi_3,m}^{\mathrm{std}}(s)
=
6(5m)^{-s}
+
O_s\left(m^{-\sigma-1}\right).
}
$$

Em módulo, para $\sigma=1/2$,

$$
\boxed{
\left|
B_{5,\chi_3,m}^{\mathrm{std}}(s)
\right|
\sim
\frac{6}{\sqrt5}
m^{-1/2}.
}
$$

Como

$$
\frac6{\sqrt5}
\approx
2.683281573,
$$

a constante assintótica também é determinada.

---

# 22. Assíntota do bracket sincronizado no exemplo

Para $p=5$,

$$
\sum_{j=1}^{2}j^2
=
1+4
=
5.
$$

Como

$$
q=3,
$$

a massa geométrica principal é

$$
q^2\sum_{j=1}^{2}j^2
=
9\cdot5
=
45.
$$

Portanto,

$$
\boxed{
\mathfrak b_{5,3,\chi_3,m}(s)
=
45\chi_3(5m)
s(s+1)
(5m)^{-s-2}
+
O_s\left(m^{-\sigma-4}\right).
}
$$

Na linha crítica,

$$
\sigma=\frac12,
$$

temos

$$
\boxed{
\left|
\mathfrak b_{5,3,\chi_3,m}(s)
\right|
=
O\left(m^{-5/2}\right).
}
$$

O expoente esperado é

$$
\boxed{-2.5}.
$$

---

# 23. Verificação numérica ilustrativa

Foi avaliado o ponto

$$
s=
\frac12
+
14.134725i.
$$

Os valores observados foram:

| $m$ | $\lvert B_{\mathrm{padrão}}\rvert$ | $\lvert B_{\mathrm{sincronizado}}\rvert$ | slope padrão | slope sincronizado |
|---:|---:|---:|---:|---:|
| $10$ | $8.2132\times10^{-1}$ | $4.1891\times10^{-1}$ | — | — |
| $100$ | $2.6820\times10^{-1}$ | $1.6152\times10^{-3}$ | $-0.4861$ | $-2.4139$ |
| $1000$ | $8.4851\times10^{-2}$ | $5.1175\times10^{-6}$ | $-0.4998$ | $-2.4992$ |
| $10000$ | $2.6833\times10^{-2}$ | $1.6183\times10^{-8}$ | $-0.5000$ | $-2.5000$ |
| $100000$ | $8.4853\times10^{-3}$ | $5.1176\times10^{-11}$ | $-0.5000$ | $-2.5000$ |

A tabela confirma os expoentes previstos:

$$
\boxed{
B_{\mathrm{padrão}}
\sim
m^{-1/2},
}
$$

e

$$
\boxed{
B_{\mathrm{sincronizado}}
\sim
m^{-5/2}.
}
$$

Esses valores são evidência numérica, não parte da prova.

---

# 24. Escopo e limitações

## 24.1 Escopo válido

A construção aplica-se diretamente a:

- caracteres de Dirichlet;
- coeficientes estritamente periódicos;
- sequências em que existe um período $q$ capaz de congelar os coeficientes sob os deslocamentos usados.

A propriedade central é

$$
a_{n+qj}=a_n.
$$

## 24.2 Multiplicatividade

A periodicidade é suficiente para recuperar o ganho local de duas potências.

A multiplicatividade é usada adicionalmente para obter a identidade global simples com

$$
L(s,\chi).
$$

## 24.3 Sequências não periódicas

Para coeficientes não periódicos, não existe necessariamente um passo finito capaz de produzir

$$
a_{c-qj}=a_c=a_{c+qj}.
$$

Portanto, o bracket sincronizado não deve ser apresentado como método universal para sequências arbitrárias.

## 24.4 Condição $\gcd(p,q)=1$

Essa condição é necessária para:

- garantir
  $$
  |\chi(p)|=1;
  $$
- fazer a multiplicação por $q$ permutar os resíduos não nulos módulo $p$;
- obter a reindexação lateral sem degeneração.

Se

$$
p\mid q,
$$

a torre central é ramificada e requer tratamento diferente.

---

# 25. Corolários consolidados

## Corolário 1 — Ganho local sincronizado

Para $pm>qh$,

$$
\boxed{
\mathfrak b_{p,q,\chi,m}(s)
=
O_{p,q,s}\left(m^{-\sigma-2}\right).
}
$$

---

## Corolário 2 — Convergência no critical strip

A série

$$
\sum_{m=1}^{\infty}
\mathfrak b_{p,q,\chi,m}(s)
$$

converge absolutamente para

$$
\boxed{
\Re(s)>-1.
}
$$

Em particular, converge em todo o critical strip.

---

## Corolário 3 — Holomorfia da carta

$$
\boxed{
\Phi_{p,q,\chi}
\text{ é holomorfa em }
\Re(s)>-1.
}
$$

---

## Corolário 4 — Identidade de reconstrução

Para $\Re(s)>1$,

$$
\boxed{
\Phi_{p,q,\chi}(s)
=
\left(
1-\chi(p)p^{1-s}
\right)L(s,\chi).
}
$$

---

## Corolário 5 — Zero-equivalência

Para

$$
0<\Re(s)<1,
$$

$$
\boxed{
\Phi_{p,q,\chi}(s)=0
\iff
L(s,\chi)=0.
}
$$

---

## Corolário 6 — Preservação de multiplicidades

No critical strip,

$$
\boxed{
\operatorname{ord}_{\rho}
\Phi_{p,q,\chi}
=
\operatorname{ord}_{\rho}
L.
}
$$

---

## Corolário 7 — Lei de colagem

Para primos $p,r$ coprimos a $q$,

$$
\boxed{
G_{r,\chi}\Phi_{p,q,\chi}
=
G_{p,\chi}\Phi_{r,q,\chi}.
}
$$

---

# 26. Rota sugerida para formalização em Lean 4

## 26.1 Definições aritméticas

Formalizar:

- caráter de Dirichlet módulo $q$;
- primo $p$ com $\gcd(p,q)=1$;
- semialcance
  $$
  h=(p-1)/2;
  $$
- conjunto de correção $\mathcal C_{p,q}$.

## 26.2 Permutação dos resíduos

Provar que

$$
\{\pm qj\bmod p:1\leq j\leq h\}
$$

é exatamente o conjunto dos resíduos não nulos módulo $p$.

## 26.3 Reindexação finita

Para truncamentos finitos, provar a bijeção entre:

- laterais $pm\pm qj$;
- inteiros não divisíveis por $p$;
- correção de fronteira.

## 26.4 Periodicidade do caráter

Provar:

$$
\chi(pm\pm qj)=\chi(pm).
$$

## 26.5 Representação integral

Definir

$$
K_{p,q}(u)
=
\sum_{j=1}^{h}(qj-|u|)_+
$$

e provar:

$$
B_{c,q}^{(p)}[f]
=
\int K_{p,q}(u)f''(c+u)\,du.
$$

## 26.6 Massa do núcleo

Provar:

$$
\int K_{p,q}
=
q^2\frac{p(p^2-1)}{24}.
$$

## 26.7 Majorante

Para $f_s(x)=x^{-s}$, provar:

$$
\left|
B_{pm,q}^{(p)}(s)
\right|
\leq
C_{p,q,s}m^{-\sigma-2}.
$$

## 26.8 Summability

Concluir `Summable` para

$$
\Re(s)>-1.
$$

## 26.9 Holomorfia

Usar convergência localmente uniforme da série de funções inteiras.

## 26.10 Ponte para a função $L$

Provar primeiro em $\Re(s)>1$:

$$
\Phi_{p,q,\chi}
=
G_{p,\chi}L.
$$

## 26.11 Zero-equivalência

Provar:

$$
0<\Re(s)<1
\Longrightarrow
G_{p,\chi}(s)\neq0.
$$

Concluir a equivalência de zeros e multiplicidades.

---

# 27. Síntese final

O bracket comum pode falhar porque a segunda diferença atua simultaneamente sobre:

- o fator analítico $n^{-s}$;
- a oscilação periódica $\chi(n)$.

O bracket sincronizado substitui os raios $j$ por

$$
qj.
$$

Pela periodicidade,

$$
\chi(c-qj)
=
\chi(c)
=
\chi(c+qj).
$$

Assim, o caráter sai em evidência e o operador volta a atuar apenas sobre a curvatura de $n^{-s}$.

A cadeia estrutural é:

$$
\boxed{
\text{periodicidade de }\chi
}
$$

$$
\downarrow
$$

$$
\boxed{
\text{passos sincronizados }qj
}
$$

$$
\downarrow
$$

$$
\boxed{
\text{fatoração exata do caráter}
}
$$

$$
\downarrow
$$

$$
\boxed{
\text{núcleo dilatado }K_{p,q}
}
$$

$$
\downarrow
$$

$$
\boxed{
\text{ganho de duas potências}
}
$$

$$
\downarrow
$$

$$
\boxed{
\text{convergência normal em }\Re(s)>-1
}
$$

$$
\downarrow
$$

$$
\boxed{
\Phi_{p,q,\chi}
=
\left(
1-\chi(p)p^{1-s}
\right)L(s,\chi)
}
$$

$$
\downarrow
$$

$$
\boxed{
\text{preservação exata dos zeros no critical strip}.
}
$$

O resultado central é:

$$
\boxed{
\Phi_{p,q,\chi}(s)
=
E_{p,q,\chi}(s)
+
\sum_{m=1}^{\infty}
\sum_{j=1}^{(p-1)/2}
\left[
a_s(pm-qj)
-2a_s(pm)
+a_s(pm+qj)
\right],
}
$$

com

$$
\boxed{
\Phi_{p,q,\chi}(s)
=
\left(
1-\chi(p)p^{1-s}
\right)L(s,\chi)
}
$$

na região original de convergência, e continuação holomorfa da carta para

$$
\boxed{
\Re(s)>-1.
}
$$

Essa construção fornece uma carta bracketada adaptada a caracteres de Dirichlet, obtida exclusivamente por periodicidade, diferenças finitas, cálculo e aritmética modular.
