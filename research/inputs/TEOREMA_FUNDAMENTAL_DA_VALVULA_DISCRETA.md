# Teorema Fundamental da Válvula Discreta

## TFVD — bracket, Green, traço e retorno

---

## 1. Ideia central

**Status matemático deste documento**

- O teorema abaixo é uma identidade algébrica exata e estritamente discreta.
- A demonstração é elementar e usa apenas diferenças finitas e somas telescópicas.
- A interpretação C2/Cp multibase é uma proposta de transporte do teorema. Ela ainda exige provar a compatibilidade entre cartas primas e identificar o bordo racional móvel com o retorno do traço.
- Nenhuma função zeta é usada na construção.

---

O Teorema Fundamental do Cálculo diz que derivar e integrar são operações inversas, desde que se conserve a informação de bordo:

$$
f(x)=f(0)+\int_0^x f'(t)\,dt.
$$

Para uma segunda derivada, a forma correspondente é

$$
f(x)=f(0)+x f'(0)+\int_0^x (x-t)f''(t)\,dt.
$$

A segunda derivada não enxerga a posição inicial nem a inclinação inicial. Esses dois dados reaparecem como condições de bordo.

O análogo discreto tem a mesma estrutura:

> **Estado = Green do bracket + retorno do traço**

$$
\text{estado}=\text{Green do bracket}+\text{retorno do traço}
$$

ou, em forma operatorial,

$$
I=\mathcal G\mathcal B+\mathsf R\,\operatorname{Tr}
$$

Essa identidade será chamada **Teorema Fundamental da Válvula Discreta**.

---

## 2. Espaços e operadores

Seja \(E\) um espaço vetorial sobre \(\mathbb R\) ou \(\mathbb C\), e fixe \(N\ge 2\).

Considere o espaço de estados discretos

$$
\mathscr F_N=E^{\{0,1,\ldots,N\}}
$$

e o espaço de defeitos interiores

$$
\mathscr D_N=E^{\{0,1,\ldots,N-2\}}.
$$

### 2.1 Primeira diferença

Para \(f\in\mathscr F_N\), defina

$$
(\Delta f)_n=f_{n+1}-f_n.
$$

### 2.2 Bracket ou curvatura discreta

Defina o bracket de segunda diferença

$$
(\mathcal Bf)_n=(\Delta^2f)_n=f_{n+2}-2f_{n+1}+f_n,\quad 0\le n\le N-2.
$$

Equivalentemente,

$$
(\mathcal Bf)_n=(\Delta f)_{n+1}-(\Delta f)_n.
$$

Portanto, \(\mathcal B\) não mede a posição nem a inclinação. Ele mede a mudança da inclinação: a **curvatura discreta**.

### 2.3 Traço discreto

Defina a porta de bordo

$$
\operatorname{Tr}f=(f_0,(\Delta f)_0)=(f_0,f_1-f_0)\in E\oplus E.
$$

O traço conserva exatamente os dois dados apagados por uma segunda diferença:

1. a posição inicial;
2. a inclinação inicial.

### 2.4 Operador de retorno

Para \((a,b)\in E\oplus E\), defina

$$
(\mathsf R(a,b))_n=a+nb,\quad 0\le n\le N.
$$

O operador \(\mathsf R\) devolve ao espaço de estados o modo afim especificado pelo traço.

### 2.5 Operador de Green discreto

Para \(g\in\mathscr D_N\), defina

$$
(\mathcal Gg)_0=(\mathcal Gg)_1=0
$$

e, para \(2\le n\le N\),

$$
(\mathcal Gg)_n=\sum_{j=0}^{n-2}(n-1-j)g_j.
$$

Seu núcleo é triangular:

$$
G(n,j)=\begin{cases}
n-1-j, & 0\le j\le n-2,\\
0, & j\ge n-1.
\end{cases}
$$

Um defeito criado em \(j\) altera a inclinação a partir de \(j\). Essa inclinação é acumulada até \(n\), produzindo o peso \(n-1-j\).

---

## 3. A válvula discreta

Defina o operador

$$
\mathcal V_N:\mathscr F_N\to\mathscr D_N\oplus E\oplus E
$$

por

$$
\mathcal V_Nf=(\mathcal Bf,\operatorname{Tr}f).
$$

A válvula separa um estado completo em dois registros:

- **registro interior:** \(\mathcal Bf\), contendo a curvatura ou defeito;
- **reservatório de bordo:** \(\operatorname{Tr}f\), contendo os modos que o bracket não enxerga.

Seu caminho inverso é

$$
\mathcal V_N^{-1}(g,a,b)=\mathcal Gg+\mathsf R(a,b).
$$

Ela é chamada válvula porque nenhum dos dois registros, isoladamente, contém o estado inteiro. O mecanismo abre o estado em corrente interior e reservatório de bordo, e depois os recombina sem perda.

---

## 4. Teorema Fundamental da Válvula Discreta

### Teorema

Para todo \(f\in\mathscr F_N\), vale

$$
f=\mathcal G\mathcal Bf+\mathsf R\operatorname{Tr}f.
$$

Coordenada por coordenada,

$$
f_n=f_0+n(f_1-f_0)+\sum_{j=0}^{n-2}(n-1-j)(\mathcal Bf)_j,
$$

com a soma interpretada como vazia para \(n=0,1\).

Além disso:

$$
\mathcal B\mathcal G=I_{\mathscr D_N},\quad \operatorname{Tr}\mathcal G=0,
$$

$$
\mathcal B\mathsf R=0,\quad \operatorname{Tr}\mathsf R=I_{E\oplus E}.
$$

Consequentemente, \(\mathcal V_N\) é um isomorfismo, com inversa

$$
\mathcal V_N^{-1}(g,a,b)=\mathcal Gg+\mathsf R(a,b).
$$

### Leitura humana

> Todo estado discreto é determinado de maneira única por sua curvatura interior e por dois dados de bordo. Integrar discretamente o bracket reconstrói o interior; o operador de retorno recoloca a posição e a inclinação que o bracket apagou.

---
