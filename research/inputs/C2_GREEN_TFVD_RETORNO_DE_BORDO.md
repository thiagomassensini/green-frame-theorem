# TFVD no Green C2: retorno discreto do bordo

## Decisão

**Sim, o Teorema Fundamental da Válvula Discreta encaixa no Green C2 — mas com uma separação importante.**

Ele fecha exatamente o **retorno geométrico finito** do bordo nas coordenadas nativas FULL-EVEN e identifica a lei do bordo móvel. Ele não remove o bloqueio aritmético mais recente: a perna `A_even_pre` ainda não desce pelo quociente J/H.

O estado correto do gate é:

```text
PASS_TFVD_C2_FINITE_VALVE_FACTORIZATION
PASS_TFVD_C2_EDGE_PAIR_RETURN
PASS_TFVD_C2_MOVING_ENDPOINT_LEDGER
PASS_TFVD_C2_LOCAL_GREEN_WEDGE
PASS_TFVD_C2_ENDPOINT_TRACE_UNIFORMLY_BOUNDED

STOP_FIXED_FINITE_TRACE_FOR_P_ONLY_BULK
STOP_FULL_CUMULATIVE_RETURN_UNBOUNDED_IN_VERTEX_L2
STOP_NATIVE_A_NONZERO_ON_COEQUALIZER_KERNEL

NEEDS_PROVENANCE_ENRICHED_VALVE_GRAPH_RELATION
```

Nenhuma consequência `Green -> zero` é emitida.

### Fronteira congelada usada

O encaixe abaixo parte dos resultados mais recentes do ledger:

- `C2_GREEN_CROSS_LAGRANGIAN_VECTOR_PORT.md`: reconstrução exata das duas arestas por ((o,p));
- `C2_GREEN_NATIVE_A_PRET0_TYPE_REGISTRY.md`: bulk tipado como (A_{\mathrm{even}}^{\mathrm{pre}}\circ\operatorname{Rec}_{(o,p)}\circ BC_{C2}^{\mathrm{cross}});
- `C2_GREEN_JH_COEQUALIZER_GRAPH_RELATION(2).md`: relação pós-T0 fechada e witness exato da falha de descida de (A);
- `C2_GREEN_CLOSED_NATIVE_ENDPOINT_GRAPH_LIFT(2).md`: fronteira atual `NEEDS_PROVENANCE_ENRICHED_GRAPH_RELATION`.

Esses resultados são tratados como entradas congeladas; o presente auditor acrescenta a fatoração de válvula e não reinterpreta os eixos (d_J), (j), (p_A), (p_T) ou (k_{\mathrm{eff}}).

## 1. A carta C2 na qual a válvula fecha

Fixe (Jgeq 1) células FULL-EVEN e um estado

$$
f=(f_1,\ldots,f_{2J+1}).
$$

Nas arestas, use

$$
x_n=(d_Vf)_n=f_{n+1}-f_n.
$$

Para a célula de centro (c=2j), com peso

$$
\omega_j=2^{-v_2(2j)}.
$$

as coordenadas cross-Lagrangian congeladas são

$$
o_j=-\frac{x_{2j-1}+x_{2j}}{\sqrt2},
\qquad
p_j=\frac{\omega_j(x_{2j}-x_{2j-1})}{\sqrt2}.
$$

Aqui (o_j) é o through-flow de valor e (p_j) é o fluxo de bracket, isto é, a curvatura ponderada do centro par. A matriz local é

$$
\binom{o_j}{p_j}
=
\frac1{\sqrt2}
\begin{pmatrix}
-1&-1\\
-\omega_j&\omega_j
\end{pmatrix}
\binom{x_{2j-1}}{x_{2j}},
\qquad \det=-\omega_j\neq0.
$$

Logo as duas arestas retornam literalmente:

$$
x_{2j-1}=-\frac{o_j}{\sqrt2}-\frac{p_j}{\sqrt2\,\omega_j},
\qquad
x_{2j}=-\frac{o_j}{\sqrt2}+\frac{p_j}{\sqrt2\,\omega_j}.
$$

Isso recupera exatamente o resultado já congelado

$$
\operatorname{Rec}_{(o,p)}BC_{C2}^{\mathrm{cross}}=d_V
$$

em todos os pares FULL-EVEN, inclusive seed e coarse.

## 2. Corolário C2 do Teorema da Válvula

Defina o bulk e o traço por

$$
\mathcal B_{C2,J}f=(p_1,\ldots,p_J),
\qquad
\operatorname{Tr}_{C2,J}f=(a,o_1,\ldots,o_J),
\qquad a=f_1.
$$

O Green lift de curvatura, com traço nulo, é local:

$$
(\mathcal G_{C2,J}p)_{2j}=-\frac{p_j}{\sqrt2\,\omega_j},
\qquad
(\mathcal G_{C2,J}p)_{2j-1}=0.
$$

O retorno de traço, com (p=0), é

$$
(\mathsf R_{C2,J}(a,o))_{2j-1}=a-\sqrt2\sum_{k<j}o_k,
$$

$$
(\mathsf R_{C2,J}(a,o))_{2j}=a-\sqrt2\sum_{k<j}o_k-\frac{o_j}{\sqrt2},
$$

$$
(\mathsf R_{C2,J}(a,o))_{2j+1}=a-\sqrt2\sum_{k\leq j}o_k.
$$

Então, exatamente,

$$
I=\mathcal G_{C2,J}\mathcal B_{C2,J}+\mathsf R_{C2,J}\operatorname{Tr}_{C2,J}.
$$

Mais que uma decomposição unilateral, as cartas são inversas dos dois lados:

$$
\mathcal B\mathcal G=I,
\quad
\operatorname{Tr}\mathsf R=I,
\quad
\operatorname{Tr}\mathcal G=0,
\quad
\mathcal B\mathsf R=0.
$$

Portanto

$$
(\mathcal B,\operatorname{Tr})^{-1}=(\mathcal G,\mathsf R).
$$

Esse é o encaixe literal do TFVD no chart nativo C2.

## 3. O bordo móvel vira uma soma de válvulas

No cutoff de (J) células, o valor do bordo direito é

$$
f_{2J+1}=a-\sqrt2\sum_{j=1}^{J}o_j.
$$

Ao mover o bordo por uma célula completa,

$$
f_{2J+3}-f_{2J+1}=-\sqrt2\,o_{J+1}.
$$

Logo o retorno pendente não é um resíduo misterioso: é o acumulado do canal (o). O fluxo (p) altera o centro da célula, mas cancela exatamente entre suas duas arestas e não muda o endpoint exterior.

Para um estado de suporte finito cujo valor final seja zero, aparece a condição de balanço

$$
a=\sqrt2\sum_{j\geq1}o_j.
$$

Esta é a condição no infinito que faltava distinguir do retorno em cada truncamento.

## 4. Compatibilidade com a identidade de Green

Na célula ((L,C,R)), use

$$
\Gamma_0f=(f_L,f_R),
\qquad
\Gamma_1f=(\omega(f_L-f_C),\omega(f_R-f_C)).
$$

Na carta de Haar,

$$
u=\frac{f_L+f_R}{\sqrt2},
\qquad
o=\frac{f_L-f_R}{\sqrt2},
$$

$$
p=\frac{\omega(f_L+f_R-2f_C)}{\sqrt2},
\qquad q^H=\omega o.
$$

O wedge odd cancela:

$$
o_fq_g^H-q_f^Ho_g=0,
$$

e a forma de bordo inteira reduz exatamente a

$$
\langle\Gamma_0f,\Gamma_1g\rangle-\langle\Gamma_1f,\Gamma_0g\rangle=u_fp_g-p_fu_g.
$$

Se

$$
(\Delta_{C2}f)_C=\omega(2f_C-f_L-f_R),
$$

então

$$
u_fp_g-p_fu_g=(\Delta_{C2}f)_C g_C-f_C(\Delta_{C2}g)_C.
$$

Assim, o retorno da válvula é compatível com a polarização Green/Stokes local já provada. Em cutoffs de células completas, todas essas identidades têm resíduo simbólico zero.

## 5. Por que o traço atual não pode ser só dois escalares

Para (J) células,

$$
\operatorname{rank}\mathcal B_{C2,J}=J,
\qquad
\dim\ker\mathcal B_{C2,J}=J+1.
$$

Consequentemente, qualquer identidade

$$
I=\mathcal G\mathcal B_{C2,J}+\mathsf R\operatorname{Tr}
$$

precisa de pelo menos (J+1) coordenadas de traço independentes sobre o kernel do bulk (p). Um traço fixo de dimensão dois não pode reconstruir uniformemente esse bulk incompleto.

Isto não contradiz o TFVD original. Para a segunda diferença completa, o kernel é o espaço afim de dimensão dois e o traço ((f_1,d_Vf_1)) basta. No C2 atual, (p) retém apenas a curvatura dos centros pares; o through-flow (o), ou uma completion equivalente por bracket mais carry, contém as coordenadas que faltam.

Há portanto duas rotas legítimas:

1. manter o traço vetorial ((a,o_1,o_2,\ldots)); ou
2. promover bracket mais carry a uma segunda diferença completa e só então comprimir o traço exterior para dimensão dois.

A segunda rota ainda exige a tipagem global do carry; ela não deve ser declarada por analogia.

## 6. Endpoint limitado não é o mesmo que retorno global limitado

No peso Hardy já usado no ledger,

$$
h_n=n(1+\log n)^2,
$$

vale

$$
\sum_{n\geq1}\frac1{h_n}\leq2.
$$

Por Cauchy–Schwarz, o endpoint é contínuo:

$$
\left|\sum_n x_n\right|\leq
\left(\sum_n\frac1{h_n}\right)^{1/2}
\left(\sum_n h_n|x_n|^2\right)^{1/2}.
$$

Logo o **valor do bordo** tem bound uniforme.

Já a reconstrução de toda a sequência por somas parciais não é uniformemente limitada desse espaço de arestas para o (ell^2) de vértices. Um witness finito é

$$
x_k=\frac1{h_k}\mathbf 1_{[r,r^2]}(k),
\qquad
a=-\sum_{k=r}^{r^2}x_k.
$$

O estado retornado forma um plateau de comprimento (r), e o quociente de normas tem lower bound que cresce como

$$
\sqrt{\frac{r}{\log r}}.
$$

Portanto o objeto global natural é um retorno fechado/não limitado, ou um operador limitado apenas depois de escolher a norma de grafo adequada. Isso concorda com a relação fechada não limitada já encontrada no endpoint contextual.

## 7. O bloqueio aritmético que a válvula não apaga

O avanço mais recente construiu o endpoint pós-T0 como relação fechada no quociente:

$$
R_Q=\operatorname{Graph}(\overline N)\subset H_Q^0\oplus H_Q^{-1}.
$$

Mas a perna (A) não desce pelo coequalizer (Q). O witness exato usa os canais (d_J=1,2):

$$
g=(1,-1),
\qquad Qg=0,
$$

enquanto

$$
A_{\mathrm{even}}^{\mathrm{pre}}g
=\begin{pmatrix}\frac12&\frac{\sqrt3}{2}\end{pmatrix}
\binom{1}{-1}
=\frac{1-\sqrt3}{2}\neq0.
$$

Logo

$$
\ker Q\not\subseteq\ker A_{\mathrm{even}}^{\mathrm{pre}},
$$

e não existe (widetilde A) no quociente atual com

$$
A_{\mathrm{even}}^{\mathrm{pre}}=\widetilde A Q.
$$

A válvula C2 é uma mudança de coordenadas invertível **antes** de (Q). Por isso ela não pode transformar esse valor não nulo em zero. O retorno geométrico está resolvido; a descida aritmética permanece bloqueada.

## 8. O próximo objeto correto

O TFVD mostra exatamente onde colocar a informação que (Q) apaga: no traço enriquecido, não dentro de uma seção reversa do quociente.

O candidato tipado é a relação

$$
\mathfrak R_{\mathrm{valv}}^{\mathrm{enr}}=
\left\{
\bigl(
Qz,\overline NQz;
A_{\mathrm{even}}^{\mathrm{pre}}z,
\operatorname{Tr}_{C2}z
\bigr):
z\in\mathcal D_{\mathrm{pre}}
\right\}.
$$

O lado tower usa o quociente somente onde ele é canônico. O lado (A) preserva

```text
p_A, tau, d_J, cell, corner, orientation, flags, role.
```

Esse objeto é uma relação enriquecida; ele não finge que (A) é função apenas de (Qz), não escolhe representante mínimo e não usa pseudoinversa.

Os gates seguintes são então claros:

1. provar que a relação enriquecida é fechada na norma de grafo correta;
2. colar seed, coarse, bracket, center rescue, carry e cutoff sem apagar a proveniência;
3. só depois testar a divisibilidade análise–valor pela síntese coerente saturada;
4. somente após isso rodar a compressão Green relevante e o gate refletido.

## Conclusão

O TFVD **resolve o retorno do bordo no nível nativo/geométrico e em todo cutoff finito**. Ele também transforma o bordo móvel numa fórmula explícita e cutoff-compatível. O que falta já não é “achar o retorno”: é manter no endpoint aritmético as coordenadas de proveniência que o quociente atual apaga.

Em uma frase:

$$
\text{retorno C2 finito: fechado;}
\qquad
\text{lift aritmético global: ainda bloqueado por }\ker Q\not\subseteq\ker A.
$$
