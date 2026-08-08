# Teorema do Frame Green de Todas as Bases

## Especificação matemática, prova, arquitetura formal e plano de repositório

**Estado deste documento:** prova matemática em papel fechada para o teorema-base; formalização Lean pendente; protótipo finito e auditorias numéricas já existentes.

**Escopo:** todas as bases inteiras \(b\ge 2\), primas ou compostas; espaços \(\ell^2\); stencils Green/TFVD de segunda ordem; frame aritmético; normalização de Parseval; reconstrução de Poisson do bulk a partir dos canais externos.

**Não depende de:** conjecturas, zeros de funções especiais, continuação analítica, equação funcional, primalidade, tabelas externas ou escolha de um parâmetro espectral privilegiado.

---

## 1. Resumo executivo

A construção distribui cada coordenada inteira \(n>1\) entre todas as bases posicionais que a enxergam verticalmente. A distribuição canônica vem da profundidade de carry

\[
k_b(n)=\max\{k\in\mathbb N:b^k\mid n\}
\]

e da escala logarítmica \(k_b(n)\log b\). Depois dessa distribuição, cada fibra \((b,n)\) é dividida ortogonalmente em:

\[
\mu_G(b,n)=\frac{\omega_b(n)}{b},
\qquad
\mu_R(b,n)=\omega_b(n)\left(1-\frac1b\right),
\]

onde \(\mu_G\) é a massa transmitida ao stencil Green e \(\mu_R\) é a massa preservada no canal residual/retorno.

O operador de análise completo

\[
T=(E,B)
\]

reúne:

- a semente \(f(1)\);
- os canais residuais;
- os stencils Green de profundidade \(1\), colocados no setor externo \(E\);
- os stencils Green de profundidade pelo menos \(2\), colocados no bulk \(B\).

A família de vetores-linha de \(T\) forma um frame de \(\ell^2(\mathbb N_{>0})\) com cotas universais explícitas:

\[
\boxed{
\frac12\|f\|^2
\le
\|Tf\|^2
\le
C_F\|f\|^2
}
\]

com

\[
C_F
=
1+
\frac32
+
12\sum_{b=2}^{\infty}\frac1{b^2}
+
3\sum_{b=2}^{\infty}\frac1{b^3}
\approx 10.8453795116575.
\]

Consequentemente, o operador de frame

\[
F=T^*T
\]

é positivo e continuamente invertível. A normalização canônica

\[
V=T F^{-1/2}
\]

é uma isometria. Escrevendo

\[
V=(E_0,B_0),
\]

o setor externo \(E_0\) é limitado inferiormente e tem imagem fechada. Por isso existe um operador de Poisson canônico e limitado

\[
M_{\mathrm{AB}}
=
B_0(E_0^*E_0)^{-1}E_0^*
\]

que satisfaz a identidade exata

\[
\boxed{
M_{\mathrm{AB}}E_0=B_0.
}
\]

Logo o bulk não precisa ser descartado nem ajustado ponto a ponto: em todo estado globalmente coerente, ele é reconstruído de forma fixa e linear a partir dos dados externos.

Para os pesos canônicos de carry, o bulk é comprovadamente não trivial. A fibra \((b,n)=(2,4)\) fornece uma cota positiva independente do cutoff.

Este é o conteúdo matemático autônomo do **Teorema do Frame Green de Todas as Bases**.

---

## 2. Leitura conceitual

A construção pode ser resumida como:

\[
\boxed{
\text{divisibilidade multibase}
\longrightarrow
\text{partição de unidade}
\longrightarrow
\text{split Green–retorno}
\longrightarrow
\text{frame}
\longrightarrow
\text{Parseval}
\longrightarrow
\text{Poisson}.
}
\]

O princípio estrutural é:

> Toda compressão enviada ao canal Green deve conservar, em um canal ortogonal explícito, a massa que não atravessou o carry.

Sem o canal residual, uma tentativa de forçar toda a massa através de todos os Green locais produz caudas e pode destruir a coerção externa. Com o split

\[
\mu_G+\mu_R=\omega,
\]

a conservação é fibra a fibra, antes de somar câmeras e antes de tomar qualquer limite.

---

## 3. Escopo e não alegações

### 3.1 O que o teorema afirma

1. Existe uma família contável explícita de vetores em \(\ell^2(\mathbb N_{>0})\) indexada por todas as bases inteiras e seus eventos de divisibilidade.
2. Essa família é um frame com cotas universais.
3. Seu operador de frame é invertível.
4. A normalização canônica produz um frame de Parseval.
5. O setor externo da realização normalizada tem imagem fechada.
6. O bulk coerente é o gráfico de um operador de Poisson limitado.
7. O bulk não colapsa identicamente na instância canônica de carry.

### 3.2 O que o teorema não afirma

1. Não afirma existência de zeros de qualquer operador.
2. Não afirma que uma energia pequena seja uma energia nula.
3. Não constrói ainda uma família espectral de Weyl dependente de parâmetro.
4. Não afirma autoadjunticidade de um operador infinito de altura.
5. Não identifica o operador de Poisson fixo com uma função de Weyl clássica.
6. Não usa primalidade.
7. Não usa uma representação complexa como parte da ontologia; os coeficientes são reais e a construção vale sobre \(\mathbb R\) ou \(\mathbb C\).
8. Não diz que todas as apresentações por bases sejam iguais; diz que elas são reunidas por uma análise conservativa comum.

---

## 4. Duas camadas do resultado

É matematicamente vantajoso separar o teorema em duas partes.

### 4.1 Teorema abstrato de partição admissível

O teorema de frame não precisa conhecer a fórmula específica de carry. Ele usa somente uma família de pesos

\[
\omega_b(n)\ge 0
\]

que satisfaça:

1. \(\omega_b(n)=0\) quando \(b\nmid n\);
2. para cada \(n>1\), apenas finitos \(b\) têm peso não nulo;
3. para cada \(n>1\),

\[
\sum_{b=2}^{\infty}\omega_b(n)=1.
\]

Chamaremos isso de **partição admissível de câmeras**.

### 4.2 Instância canônica de carry

A geometria de carry escolhe uma partição admissível particular:

\[
\omega_b^{\mathrm{carry}}(n)
=
\frac{k_b(n)\log b}
{\displaystyle\sum_{c=2}^{n} k_c(n)\log c},
\qquad n>1,
\]

com \(\omega_b^{\mathrm{carry}}(n)=0\) quando \(b\nmid n\).

Assim, a prova deve ser organizada da seguinte forma:

```text
partição admissível abstrata
    -> teorema universal de frame
    -> corolário para os pesos canônicos de carry
    -> witness de bulk não trivial
```

Essa separação torna a biblioteca reutilizável para outros esquemas de pesos, famílias selecionadas de bases e partições adaptativas.

---

# Parte I — Camada aritmética

## 5. Profundidade posicional

Para \(b\ge2\) e \(n\ge1\), defina

\[
k_b(n)
=
\max\{k\in\mathbb N:b^k\mid n\}.
\]

Equivalentemente, escreva de modo único

\[
n=b^{k_b(n)}m,
\qquad
b\nmid m.
\]

A função \(k_b\) é uma profundidade posicional para bases arbitrárias. Para base composta, ela não precisa satisfazer todas as leis de uma valoração prima; isso não é necessário.

### Lema 5.1 — suporte finito

Para \(n\ge1\),

\[
k_b(n)>0
\quad\Longleftrightarrow\quad
b\mid n.
\]

Se \(k_b(n)>0\), então \(2\le b\le n\). Logo, para \(n\) fixo, somente finitos \(b\) são ativos.

### Lema 5.2 — profundidade máxima

\[
b^{k_b(n)}\mid n,
\qquad
b^{k_b(n)+1}\nmid n.
\]

### Lema 5.3 — caso unitário

\[
k_b(1)=0
\]

para toda base \(b\ge2\).

---

## 6. Atividade multibase e partição canônica

Defina a atividade vertical da base \(b\) em \(n\) por

\[
x_b(n)=k_b(n)\log b.
\]

Para \(n>1\), defina o normalizador de todas as bases

\[
\mathcal A(n)
=
\sum_{b=2}^{n}x_b(n).
\]

### Lema 6.1 — positividade do normalizador

Para \(n>1\),

\[
\mathcal A(n)>0.
\]

**Prova.** A base \(b=n\) é ativa, \(k_n(n)=1\), e \(\log n>0\). Portanto um dos termos é estritamente positivo. \(\square\)

### Definição 6.2 — pesos de carry

Para \(n>1\),

\[
\omega_b(n)
=
\frac{x_b(n)}{\mathcal A(n)}.
\]

Para \(n=1\), ponha \(\omega_b(1)=0\).

### Teorema 6.3 — partição de unidade multibase

Para todo \(n>1\),

\[
\omega_b(n)\ge0,
\qquad
\omega_b(n)=0 \text{ se } b\nmid n,
\]

e

\[
\boxed{
\sum_{b=2}^{\infty}\omega_b(n)=1.
}
\]

A soma é finita para cada \(n\).

---

## 7. O subatlas primo como caso particular

Se a soma for restrita somente às bases primas, então

\[
k_p(n)=v_p(n)
\]

e

\[
\sum_{p\mid n}v_p(n)\log p=\log n.
\]

Logo a partição prima correspondente é

\[
\omega_p^{\mathrm{prime}}(n)
=
\frac{v_p(n)\log p}{\log n}.
\]

O atlas de todas as bases não é a mesma normalização do atlas primo: bases compostas acrescentam redundância deliberada. O teorema principal aceita ambos como instâncias de uma partição admissível.

---

## 8. Resolução horizontal–vertical

Fixe uma base \(a\ge2\). Considere o subespaço horizontal

\[
H_a^{\mathrm{hor}}
=
\{f\in\ell^2:f(n)=0 \text{ sempre que } a\mid n\}.
\]

Defina a análise elementar

\[
(Af)(b,n)=\sqrt{\omega_b(n)}f(n),
\]

mais a semente \(f(1)\).

Como \(\sum_b\omega_b(n)=1\), temos

\[
\|Af\|^2=\|f\|^2.
\]

Além disso, se \(f\in H_a^{\mathrm{hor}}\), então o canal vertical da própria base \(a\) é zero. Portanto

\[
\boxed{
\|f\|^2
=
|f(1)|^2+
\sum_{\substack{b\ne a\\n>1}}
\omega_b(n)|f(n)|^2.
}
\]

Esta é a forma exata da frase:

> a horizontal de uma base é resolvida pelas verticais das outras bases, com a semente \(n=1\) preservada como porto de bordo.

---

## 9. Lema aritmético de carga: profundidade um não desaparece

Defina

\[
\mathcal A_1(n)
=
\sum_{\substack{b\ge2\\k_b(n)=1}}
k_b(n)\log b
=
\sum_{\substack{b\ge2\\k_b(n)=1}}\log b
\]

e

\[
\mathcal A_{\ge2}(n)
=
\sum_{\substack{b\ge2\\k_b(n)\ge2}}
k_b(n)\log b.
\]

### Teorema 9.1 — cota de carga endpoint–bulk

Para todo \(n>1\),

\[
\boxed{
\mathcal A_{\ge2}(n)\le 2\mathcal A_1(n).
}
\]

Consequentemente,

\[
\boxed{
\frac{\mathcal A_1(n)}{\mathcal A(n)}
\ge\frac13.
}
\]

### Prova

Se \(k_b(n)\ge2\), então \(b^2\mid n\), logo \(b\le\sqrt n\).

#### Caso 1: \(b<\sqrt n\)

Defina

\[
c=\frac nb.
\]

Então \(c>\sqrt n\), \(c\mid n\), e \(c^2>n\). Portanto \(k_c(n)=1\).

O mapa \(b\mapsto n/b\) é injetivo. Além disso,

\[
k_b(n)\log b\le\log n=\log b+\log c<2\log c.
\]

Assim, a atividade bulk de \(b\) pode ser carregada em, no máximo, duas vezes a atividade depth-one de \(c\).

#### Caso 2: \(b=\sqrt n\)

Então \(n=b^2\), \(k_b(n)=2\), e

\[
k_b(n)\log b
=
2\log b
=
\log n.
\]

A base \(c=n\) possui profundidade \(1\), portanto esse termo é carregado exatamente em \(x_n(n)=\log n\).

Somando e usando a injetividade das cargas, obtemos

\[
\mathcal A_{\ge2}(n)\le2\mathcal A_1(n).
\]

\(\square\)

### Observação

Este lema fortalece a leitura geométrica do atlas: mesmo antes de introduzir o canal residual, uma fração uniforme da atividade logarítmica permanece em bases que veem \(n\) na primeira profundidade.

Ele não é necessário para a primeira cota inferior do frame, mas é útil para:

- melhorar constantes;
- estudar frames sem canal residual;
- controlar o setor endpoint Green;
- investigar minimalidade da família de bases.

---

# Parte II — Split pitagórico e stencil Green

## 10. Razão de carry

Para cada base \(b\ge2\), defina

\[
q_b=b^{-1/2}.
\]

Então

\[
q_b^2=\frac1b.
\]

---

## 11. Split Green–retorno

Para uma partição admissível \(\omega\), defina

\[
\mu_G(b,n)=\omega_b(n)q_b^2
=\frac{\omega_b(n)}b
\]

e

\[
\mu_R(b,n)=\omega_b(n)(1-q_b^2)
=
\omega_b(n)\left(1-\frac1b\right).
\]

### Teorema 11.1 — Pitágoras fibra a fibra

Para todo \(n>1\),

\[
\boxed{
\sum_b\left(\mu_G(b,n)+\mu_R(b,n)\right)=1.
}
\]

### Corolário 11.2 — massa residual uniforme

Como \(b\ge2\),

\[
1-\frac1b\ge\frac12.
\]

Logo

\[
\boxed{
\frac12
\le
\sum_b\mu_R(b,n)
\le1.
}
\]

### Corolário 11.3 — massa Green

\[
\boxed{
0<
\sum_b\mu_G(b,n)
\le\frac12.
}
\]

A desigualdade estrita vale em toda partição que realmente cubra \(n\).

---

## 12. Decomposição em torres

Para base \(b\), cada inteiro \(n\ge1\) pertence à torre única

\[
m,\;bm,\;b^2m,\ldots,
\qquad b\nmid m.
\]

Se

\[
x_k=f(b^km),
\]

então o stencil Green normalizado é

\[
(\widehat A_bx)_k
=
x_k-2q_bx_{k-1}+q_b^2x_{k-2},
\qquad k\ge2,
\]

e na primeira profundidade,

\[
(\widehat A_bx)_1
=
x_1-2q_bx_0.
\]

Isso é a forma causal truncada de

\[
\widehat A_b=(I-q_bS)^2,
\]

onde \(S\) é o shift para o ancestral da torre.

---

## 13. Fórmula global do stencil

Para \(b\mid n\), defina

\[
\mathcal D_bf(n)
=
f(n)
-
2q_b f(n/b)
+
\mathbf 1_{b^2\mid n}\,q_b^2f(n/b^2).
\]

O indicador remove o terceiro termo na primeira profundidade.

Defina o coeficiente Green:

\[
(Gf)(b,n)
=
\sqrt{\mu_G(b,n)}\,\mathcal D_bf(n).
\]

---

# Parte III — Espaços de Hilbert e operadores

## 14. Espaço de estado

Seja

\[
H=\ell^2(\mathbb N_{>0};\mathbb K),
\qquad
\mathbb K\in\{\mathbb R,\mathbb C\}.
\]

A construção usa apenas coeficientes reais. A versão complexa é a complexificação da versão real.

---

## 15. Conjuntos de índices

Defina

\[
\mathcal I
=
\{(b,n):b\ge2,\;n>1,\;b\mid n\}.
\]

Separe:

\[
\mathcal I_1
=
\{(b,n)\in\mathcal I:k_b(n)=1\},
\]

\[
\mathcal I_{\ge2}
=
\{(b,n)\in\mathcal I:k_b(n)\ge2\}.
\]

Espaços de portos:

\[
K_R=\ell^2(\mathcal I),
\qquad
K_1=\ell^2(\mathcal I_1),
\qquad
K_{\ge2}=\ell^2(\mathcal I_{\ge2}).
\]

O espaço externo é

\[
K_{\mathrm{ext}}
=
\mathbb K\oplus K_R\oplus K_1.
\]

O espaço full é

\[
K_{\mathrm{full}}
=
K_{\mathrm{ext}}\oplus K_{\ge2}.
\]

---

## 16. Operador residual

Defina inicialmente em sequências finitamente suportadas:

\[
(Rf)(b,n)
=
\sqrt{\mu_R(b,n)}f(n).
\]

Por Tonelli,

\[
\|Rf\|^2
=
\sum_{n>1}
\left(
\sum_b\mu_R(b,n)
\right)|f(n)|^2.
\]

Logo

\[
\frac12\sum_{n>1}|f(n)|^2
\le
\|Rf\|^2
\le
\sum_{n>1}|f(n)|^2.
\]

---

## 17. Operadores Green externo e bulk

Seja \(G_1\) a restrição de \(G\) às linhas de \(\mathcal I_1\), e \(G_{\ge2}\) a restrição às linhas de \(\mathcal I_{\ge2}\).

Defina

\[
Ef
=
\left(
f(1),Rf,G_1f
\right)
\in K_{\mathrm{ext}}
\]

e

\[
Bf=G_{\ge2}f\in K_{\ge2}.
\]

Finalmente,

\[
Tf=(Ef,Bf).
\]

A ortogonalidade dos espaços de coordenadas dá

\[
\|Tf\|^2
=
|f(1)|^2+\|Rf\|^2+\|Gf\|^2.
\]

---

# Parte IV — Teorema principal

## 18. Constantes universais

Defina as séries positivas convergentes

\[
S_2=\sum_{b=2}^{\infty}\frac1{b^2},
\qquad
S_3=\sum_{b=2}^{\infty}\frac1{b^3}.
\]

Defina

\[
C_G
=
\frac32+12S_2+3S_3
\approx9.8453795116575
\]

e

\[
C_F=1+C_G
\approx10.8453795116575.
\]

Essas constantes são explícitas e não são alegadas como ótimas.

Também defina

\[
\alpha=\frac1{2C_F}
\approx0.0461025821606850
\]

e

\[
\beta=\frac1{4C_F}
\approx0.0230512910803425.
\]

---

## 19. Teorema do Frame Green de Todas as Bases

### Teorema 19.1 — forma abstrata

Se \(\omega\) é uma partição admissível de câmeras, então o operador \(T\), inicialmente definido no core finitamente suportado, estende-se de maneira única a um operador linear limitado

\[
T:H\longrightarrow K_{\mathrm{full}}
\]

e satisfaz, para todo \(f\in H\),

\[
\boxed{
\frac12\|f\|^2
\le
\|Tf\|^2
\le
C_F\|f\|^2.
}
\]

Consequentemente, as linhas de \(T\) formam um frame de \(H\) com frame bounds

\[
A=\frac12,
\qquad
B=C_F.
\]

### Teorema 19.2 — forma de operador

O operador de frame

\[
F=T^*T
\]

satisfaz

\[
\boxed{
\frac12I\le F\le C_FI.
}
\]

Em particular, \(F\) é positivo, autoadjunto e invertível, com

\[
\|F^{-1}\|\le2.
\]

### Teorema 19.3 — normalização canônica

Defina

\[
V=TF^{-1/2}.
\]

Então

\[
\boxed{
V^*V=I.
}
\]

Logo \(V\) é uma isometria e as linhas normalizadas formam o frame de Parseval canônico associado a \(T\).

---

# Parte V — Prova do teorema principal

## 20. Cota inferior

Como \(G_1\) e \(B\) contribuem com termos não negativos,

\[
\|Tf\|^2
\ge
|f(1)|^2+\|Rf\|^2.
\]

Pelo Corolário 11.2,

\[
\|Rf\|^2
\ge
\frac12\sum_{n>1}|f(n)|^2.
\]

Portanto,

\[
|f(1)|^2+\|Rf\|^2
\ge
\frac12|f(1)|^2
+
\frac12\sum_{n>1}|f(n)|^2
=
\frac12\|f\|^2.
\]

Assim,

\[
\boxed{
\|Tf\|^2\ge\frac12\|f\|^2.
}
\]

---

## 21. Cota superior do setor semente–residual

Pelo mesmo cálculo,

\[
|f(1)|^2+\|Rf\|^2
\le
|f(1)|^2+\sum_{n>1}|f(n)|^2
=
\|f\|^2.
\]

Logo resta provar

\[
\|Gf\|^2\le C_G\|f\|^2.
\]

---

## 22. Cota Bessel do Green

Temos

\[
\|Gf\|^2
=
\sum_{\substack{b\ge2\\b\mid n}}
\frac{\omega_b(n)}b
\left|
f(n)-2b^{-1/2}f(n/b)
+
\mathbf1_{b^2\mid n}b^{-1}f(n/b^2)
\right|^2.
\]

Use

\[
|u+v+w|^2
\le
3(|u|^2+|v|^2+|w|^2).
\]

A soma se divide em três parcelas.

### 22.1 Termo atual

\[
L
=
3\sum_n|f(n)|^2
\sum_b\frac{\omega_b(n)}b.
\]

Como \(b\ge2\),

\[
\sum_b\frac{\omega_b(n)}b
\le
\frac12\sum_b\omega_b(n)
=
\frac12.
\]

Logo

\[
L\le\frac32\|f\|^2.
\]

### 22.2 Primeiro ancestral

A contribuição é limitada por

\[
P
=
12
\sum_{\substack{b\ge2\\b\mid n}}
\frac{\omega_b(n)}{b^2}
|f(n/b)|^2.
\]

Reindexe \(n=bm\). Como \(0\le\omega_b(bm)\le1\),

\[
P
\le
12\sum_{b=2}^{\infty}\frac1{b^2}
\sum_{m=1}^{\infty}|f(m)|^2.
\]

Portanto,

\[
P\le12S_2\|f\|^2.
\]

### 22.3 Segundo ancestral

A contribuição é

\[
Q
=
3
\sum_{\substack{b\ge2\\b^2\mid n}}
\frac{\omega_b(n)}{b^3}
|f(n/b^2)|^2.
\]

Reindexe \(n=b^2m\) e use \(\omega_b(b^2m)\le1\):

\[
Q
\le
3\sum_{b=2}^{\infty}\frac1{b^3}
\sum_{m=1}^{\infty}|f(m)|^2.
\]

Logo

\[
Q\le3S_3\|f\|^2.
\]

### 22.4 Conclusão

\[
\|Gf\|^2
\le
\left(
\frac32+12S_2+3S_3
\right)\|f\|^2
=
C_G\|f\|^2.
\]

Assim,

\[
\|Tf\|^2
\le
(1+C_G)\|f\|^2
=
C_F\|f\|^2.
\]

A estimativa prova simultaneamente:

1. que \(Gf\in\ell^2(\mathcal I)\);
2. que \(G\) é limitado no core;
3. que \(G\), \(E\), \(B\) e \(T\) se estendem por continuidade;
4. que a cota superior é uniforme em todas as bases e em todos os cutoffs.

\(\square\)

---

## 23. Invertibilidade do operador de frame

Das cotas quadráticas,

\[
\frac12I\le T^*T\le C_FI.
\]

Logo o espectro de \(F=T^*T\) está contido em

\[
\left[\frac12,C_F\right].
\]

Portanto \(F^{-1}\), \(F^{1/2}\) e \(F^{-1/2}\) são operadores limitados definidos pelo cálculo funcional contínuo.

Finalmente,

\[
V^*V
=
F^{-1/2}T^*TF^{-1/2}
=
F^{-1/2}FF^{-1/2}
=
I.
\]

\(\square\)

---

# Parte VI — Reconstrução e frame dual

## 24. Reconstrução canônica do estado

Como \(F\) é invertível,

\[
\boxed{
f=F^{-1}T^*Tf.
}
\]

Em linguagem de frames, se \((\tau_j)_j\) são os vetores-linha de \(T\), então

\[
f
=
\sum_j
\langle f,\tau_j\rangle F^{-1}\tau_j,
\]

com convergência incondicional em \(H\).

A família

\[
(F^{-1}\tau_j)_j
\]

é o frame dual canônico.

Para o frame de Parseval normalizado,

\[
f=V^*Vf.
\]

---

## 25. Estabilidade

A cota inferior implica

\[
\boxed{
\|f\|\le\sqrt2\,\|Tf\|.
}
\]

Portanto o estado global é estável em relação às coordenadas completas do atlas. Se

\[
Tf=Tg,
\]

então \(f=g\).

Mais geralmente,

\[
\|f-g\|
\le
\sqrt2\,\|Tf-Tg\|.
\]

Essa é uma desigualdade de estabilidade independente de qualquer órbita especial.

---

# Parte VII — Poisson canônico

## 26. Decomposição da isometria normalizada

Escreva

\[
V=(E_0,B_0),
\]

onde

\[
E_0=EF^{-1/2},
\qquad
B_0=BF^{-1/2}.
\]

Como \(V^*V=I\),

\[
\boxed{
E_0^*E_0+B_0^*B_0=I.
}
\]

---

## 27. Cota inferior do setor externo normalizado

Sabemos que

\[
E^*E\ge\frac12I.
\]

Logo

\[
E_0^*E_0
=
F^{-1/2}E^*EF^{-1/2}
\ge
\frac12F^{-1}.
\]

Como \(F\le C_FI\),

\[
F^{-1}\ge\frac1{C_F}I.
\]

Portanto

\[
\boxed{
E_0^*E_0\ge\alpha I,
\qquad
\alpha=\frac1{2C_F}.
}
\]

Em particular,

\[
\|E_0f\|\ge\sqrt\alpha\,\|f\|.
\]

Logo \(E_0\) é injetivo e \(\operatorname{ran}E_0\) é fechada.

---

## 28. Inversa à esquerda externa

Defina

\[
S_E
=
(E_0^*E_0)^{-1}E_0^*.
\]

Então

\[
\boxed{
S_EE_0=I.
}
\]

Além disso,

\[
\|S_E\|
\le
\alpha^{-1/2}
=
\sqrt{2C_F}.
\]

---

## 29. Projetor de compatibilidade externa

Defina

\[
\Pi_E
=
E_0S_E
=
E_0(E_0^*E_0)^{-1}E_0^*.
\]

Então \(\Pi_E\) é o projetor ortogonal sobre \(\operatorname{ran}E_0\).

Dados externos arbitrários \(y\in K_{\mathrm{ext}}\) podem ser incompatíveis com um único estado global. O vetor

\[
\Pi_Ey
\]

é sua parte coerente.

---

## 30. Operador de Poisson all-bases

Defina

\[
\boxed{
M_{\mathrm{AB}}
=
B_0S_E
=
B_0(E_0^*E_0)^{-1}E_0^*.
}
\]

Então

\[
\boxed{
M_{\mathrm{AB}}E_0=B_0.
}
\]

Esta identidade vale para todo \(f\in H\):

\[
M_{\mathrm{AB}}(E_0f)=B_0f.
\]

Não há ajuste em \(f\), em tempo, em cutoff ou em câmera.

### Cota de norma

Para \(y=E_0f\),

\[
\|M_{\mathrm{AB}}y\|^2
=
\|B_0f\|^2
=
\|f\|^2-\|E_0f\|^2.
\]

Como \(\|E_0f\|^2\ge\alpha\|f\|^2\),

\[
\|B_0f\|^2
\le
\frac{1-\alpha}{\alpha}\|E_0f\|^2.
\]

No complemento ortogonal de \(\operatorname{ran}E_0\), \(S_E\) é zero. Portanto

\[
\boxed{
\|M_{\mathrm{AB}}\|
\le
\sqrt{\frac{1-\alpha}{\alpha}}
=
\sqrt{2C_F-1}
\approx4.54870959980026.
}
\]

A constante é universal e não ótima.

---

## 31. Completude de Poisson

Defina

\[
P_{\mathrm{AB}}
=
VS_E:
K_{\mathrm{ext}}
\longrightarrow
K_{\mathrm{full}}.
\]

Então

\[
P_{\mathrm{AB}}y
=
\left(
\Pi_Ey,
M_{\mathrm{AB}}y
\right).
\]

E

\[
\boxed{
P_{\mathrm{AB}}E_0=V.
}
\]

Portanto o atlas coerente completo é reconstruído a partir do endpoint normalizado.

---

## 32. A imagem coerente é um gráfico

Como \(E_0\) é injetivo,

\[
\operatorname{ran}V
=
\left\{
(E_0f,B_0f):f\in H
\right\}.
\]

Usando o operador de Poisson,

\[
\boxed{
\operatorname{ran}V
=
\left\{
(y,M_{\mathrm{AB}}y):
y\in\operatorname{ran}E_0
\right\}.
}
\]

Logo o subespaço globalmente coerente do atlas é o gráfico fechado de um operador limitado sobre uma imagem externa fechada.

Esta é a formulação geométrica mais forte do resultado.

---

# Parte VIII — Bulk não trivial

## 33. Witness canônico \((b,n)=(2,4)\)

Para os pesos log-depth de carry, as bases ativas em \(n=4\) são \(2\) e \(4\):

\[
x_2(4)=2\log2=\log4,
\qquad
x_4(4)=\log4.
\]

Logo

\[
\omega_2(4)=\frac12.
\]

Como

\[
q_2^2=\frac12,
\]

temos

\[
\mu_G(2,4)
=
\frac{\omega_2(4)}2
=
\frac14.
\]

A linha Green bulk correspondente é

\[
\sqrt{\frac14}
\left(
e_4-2q_2e_2+q_2^2e_1
\right).
\]

Aplicada a \(e_4\), ela produz \(1/2\). Portanto

\[
\|Be_4\|^2\ge\frac14.
\]

Logo

\[
B\ne0.
\]

---

## 34. Bulk após normalização

Seja

\[
u=F^{1/2}e_4.
\]

Então

\[
B_0u
=
BF^{-1/2}F^{1/2}e_4
=
Be_4.
\]

Além disso,

\[
\|u\|^2
=
\langle Fe_4,e_4\rangle
\le C_F.
\]

Portanto

\[
\boxed{
\|B_0\|^2
\ge
\frac1{4C_F}
=
\beta.
}
\]

Assim,

\[
\boxed{
\|B_0\|
\ge
\frac1{2\sqrt{C_F}}
\approx0.151826516394016.
}
\]

O bulk permanece vivo depois da normalização de Parseval.

---

## 35. O operador de Poisson é não nulo

Escolha \(f\) unitário com

\[
\|B_0f\|^2\ge\beta.
\]

Então

\[
\|E_0f\|^2
=
1-\|B_0f\|^2
\le1-\beta.
\]

Como

\[
M_{\mathrm{AB}}E_0f=B_0f,
\]

segue

\[
\boxed{
\|M_{\mathrm{AB}}\|
\ge
\sqrt{\frac{\beta}{1-\beta}}
\approx0.153607261185828.
}
\]

Logo a extensão externa–bulk não é uma operação vazia.

---

# Parte IX — Versão finita e convergência

## 36. Seções finitas

Defina

\[
H_N=\operatorname{span}\{e_1,\ldots,e_N\}.
\]

Para \(n\le N\), toda base ativa satisfaz \(b\le n\le N\). Logo a partição de pesos é completa dentro do cutoff.

Defina os índices finitos

\[
\mathcal I_N
=
\{(b,n)\in\mathcal I:b\le N,\;n\le N\}.
\]

O operador finito \(T_N\) usa:

- estado em \(H_N\);
- todas as bases \(2\le b\le N\);
- todas as linhas com \(n\le N\);
- o mesmo split \(\mu_G,\mu_R\);
- o mesmo stencil.

---

## 37. Cotas uniformes finitas

Em \(H_N\),

\[
\boxed{
\frac12I_{H_N}
\le
T_N^*T_N
\le
C_FI_{H_N}.
}
\]

As constantes não dependem de \(N\).

Isso é mais forte do que apenas verificar numericamente que cada matriz é invertível.

---

## 38. Convergência forte do operador de análise

Sejam \(P_N\) as projeções de estado em \(H_N\) e \(Q_N\) as projeções crescentes nos portos finitos.

Embuta \(T_N\) no espaço infinito por

\[
\widetilde T_N
=
Q_NTP_N.
\]

Então

\[
\boxed{
\widetilde T_N
\longrightarrow T
\quad\text{fortemente}.
}
\]

### Prova

Para \(f\in H\),

\[
\|\widetilde T_Nf-Tf\|
\le
\|Q_NT(P_Nf-f)\|
+
\|(Q_N-I)Tf\|.
\]

O primeiro termo tende a zero pela limitação de \(T\) e por \(P_Nf\to f\). O segundo tende a zero porque \(Q_N\to I\) fortemente no codomínio. \(\square\)

---

## 39. Convergência dos operadores de frame

Defina

\[
F_N=P_NT^*Q_NTP_N.
\]

Então

\[
F_N\to F
\]

fortemente, após a identificação natural das seções.

Para evitar o kernel no complemento de \(H_N\), defina

\[
\widehat F_N
=
F_N+(I-P_N).
\]

As cotas uniformes dão um intervalo espectral comum separado de zero. Portanto, pelo cálculo funcional contínuo,

\[
\widehat F_N^{-1/2}
\longrightarrow
F^{-1/2}
\]

fortemente.

Esse é o caminho rigoroso para demonstrar

\[
V_N
=
T_NF_N^{-1/2}
\longrightarrow
V
\]

em uma realização comum.

---

## 40. Convergência dos operadores de Poisson

A convergência de

\[
M_N
=
B_{0,N}(E_{0,N}^*E_{0,N})^{-1}E_{0,N}^*
\]

para \(M_{\mathrm{AB}}\) deve ser formalizada depois da convergência de \(V_N\).

O ingrediente decisivo já existe: a cota inferior uniforme

\[
E_{0,N}^*E_{0,N}\ge\alpha I.
\]

Ela impede que as pseudoinversas explodam.

### Status

- identidade \(M_NE_{0,N}=B_{0,N}\): exata em cada cutoff;
- normas finitas: calculadas;
- cota uniforme abstrata: provada acima;
- convergência forte \(M_N\to M_{\mathrm{AB}}\): próximo teorema de aproximação, não necessário para a existência do operador infinito.

---

# Parte X — Evidência finita já existente

## 41. Auditoria numérica atual

A implementação finita já calcula o menor autovalor generalizado do setor externo normalizado e a norma do completor de Poisson.

| \(N\) | menor energia externa normalizada | norma do bulk normalizado | norma de Poisson |
|---:|---:|---:|---:|
| 8 | 0.4282931698 | 0.7561129745 | 1.1553567770 |
| 16 | 0.4073143994 | 0.7698607670 | 1.2062777194 |
| 32 | 0.4147536936 | 0.7650139256 | 1.1878844838 |
| 64 | 0.4213999062 | 0.7606576719 | 1.1717690765 |
| 128 | 0.4257324027 | 0.7578044585 | 1.1614186702 |
| 256 | 0.4280573587 | 0.7562688948 | 1.1559132836 |

No cutoff \(N=256\), a auditoria também registra:

\[
\|V^*V-I\|
\approx9.98\times10^{-15}
\]

e

\[
\|M_NE_{0,N}-B_{0,N}\|
\approx3.38\times10^{-15}.
\]

### Interpretação correta

1. Os dados confirmam a álgebra finita.
2. As constantes universais da prova são conservadoras.
3. Os dados sugerem uma cota externa ótima muito maior que \(\alpha\).
4. Os dados não substituem a prova infinita.
5. Nenhuma extrapolação numérica é usada no Teorema 19.1.

---

# Parte XI — Programa de constantes ótimas

## 42. Por que a constante atual é larga

A prova usa três relaxações fortes:

1. a desigualdade uniforme

\[
|u+v+w|^2\le3(|u|^2+|v|^2+|w|^2);
\]

2. a remoção dos pesos aritméticos nos ancestrais:

\[
\omega_b(n)\le1;
\]

3. a soma sobre todas as bases, mesmo quando muitas não podem estar simultaneamente ativas em uma coordenada.

A auditoria finita apresenta máximo bruto do frame próximo de \(3.82\), enquanto a cota teórica atual é \(10.845\).

---

## 43. Rotas para melhorar a cota superior

### 43.1 Young ponderada

Usar, para parâmetros positivos escolhidos em função de \(b\),

\[
|u+v+w|^2
\le
(1+\lambda+\mu)
\left(
|u|^2+\lambda^{-1}|v|^2+\mu^{-1}|w|^2
\right).
\]

### 43.2 Schur no Gram infinito

Abrir

\[
G^*G
\]

como uma matriz esparsa sobre o grafo multiplicativo

\[
n\leftrightarrow bn\leftrightarrow b^2n
\]

e aplicar um teste de Schur com peso aritmético.

### 43.3 Usar a atividade real

Em vez de \(\omega_b(n)\le1\), explorar

\[
\omega_b(n)
=
\frac{k_b(n)\log b}{\mathcal A(n)}.
\]

### 43.4 Separar profundidade um e bulk

O Lema 9.1 garante uma fração uniforme da atividade em profundidade um. Isso pode produzir uma cota externa melhor sem depender apenas do residual.

---

## 44. Problema de constante ótima

Defina

\[
A_\star
=
\inf_{\|f\|=1}\|Tf\|^2,
\qquad
B_\star
=
\sup_{\|f\|=1}\|Tf\|^2.
\]

Problemas independentes e bem definidos:

1. determinar ou estimar \(A_\star\);
2. determinar ou estimar \(B_\star\);
3. decidir se os extremos são atingidos;
4. estudar a estabilidade das constantes sob remoção de famílias de bases;
5. determinar o número mínimo de câmeras necessário para manter uma cota inferior uniforme.

---

# Parte XII — Relação com a TFVD e conservação de Bessel

## 45. O stencil não é inserido depois

O stencil

\[
\mathcal D_bf(n)
=
f(n)-2q_bf(n/b)+q_b^2f(n/b^2)
\]

é a forma quadraticamente normalizada do bracket vertical vestido pela razão física

\[
q_b=b^{-1/2}.
\]

Não existe uma matriz de calibração posterior.

---

## 46. Estado completo versus readout

A normalização \(V\) conserva o estado:

\[
V^*V=I.
\]

A projeção em apenas alguns canais pode anular um readout sem anular o estado. O teorema torna isso explícito:

\[
\|f\|^2
=
\|E_0f\|^2+\|B_0f\|^2.
\]

O canal bulk é ortogonal ao externo no codomínio, mas ambos vêm do mesmo estado.

---

## 47. Ledger pitagórico

Para todo \(f\),

\[
\boxed{
\|f\|^2
=
\|E_0f\|^2+\|B_0f\|^2.
}
\]

Para qualquer dado externo coerente \(y=E_0f\),

\[
\|f\|^2
=
\|y\|^2+\|M_{\mathrm{AB}}y\|^2.
\]

Esta é uma forma global de conservação Bessel/Green.

---

# Parte XIII — Formulação paper-ready

## 48. Abstract em inglês

> **All-Bases Green Frame Theorem.**  
> We construct a countable arithmetic frame on \(\ell^2(\mathbb N_{>0})\) from all positional bases \(b\ge2\). Each integer coordinate is distributed among its active bases by a finite partition of unity, canonically realized by logarithmic carry depth. The mass assigned to every base is split into a Green-transmitted channel of weight \(\omega_b(n)/b\) and an orthogonal residual-return channel of weight \(\omega_b(n)(1-1/b)\). The associated carry-normalized second-difference stencils, together with the residual and seed channels, form a frame with explicit cutoff-independent bounds. Its canonical Parseval normalization has a closed external range, and the coherent bulk is the graph of a bounded Poisson operator over that range. For the logarithmic carry partition the normalized bulk is nontrivial. The construction is independent of primality and of any special-function zero problem.

---

## 49. Enunciado compacto para artigo

### Theorem

Let \(\omega_b(n)\) be an admissible camera partition. Set \(q_b=b^{-1/2}\), and for \(b\mid n\) define

\[
r_{b,n}
=
\sqrt{\omega_b(n)(1-b^{-1})}\,e_n,
\]

\[
g_{b,n}
=
\sqrt{\frac{\omega_b(n)}b}
\left(
e_n-2b^{-1/2}e_{n/b}
+
\mathbf1_{b^2\mid n}b^{-1}e_{n/b^2}
\right).
\]

Then the countable family

\[
\mathcal F
=
\{e_1\}
\cup
\{r_{b,n}\}_{b\mid n}
\cup
\{g_{b,n}\}_{b\mid n}
\]

is a frame for \(\ell^2(\mathbb N_{>0})\) with bounds

\[
\frac12
\quad\text{and}\quad
1+\frac32
+12\sum_{b=2}^{\infty}b^{-2}
+3\sum_{b=2}^{\infty}b^{-3}.
\]

If \(\mathcal F\) is split into the external vectors

\[
\{e_1\}\cup\{r_{b,n}\}\cup\{g_{b,n}:k_b(n)=1\}
\]

and the bulk vectors

\[
\{g_{b,n}:k_b(n)\ge2\},
\]

then the canonical Parseval analysis \(V=(E_0,B_0)\) satisfies:

1. \(E_0\) is bounded below;
2. \(\operatorname{ran}E_0\) is closed;
3. there is a bounded operator \(M_{\mathrm{AB}}\) with

\[
M_{\mathrm{AB}}E_0=B_0;
\]

4. \(\operatorname{ran}V\) is the graph of \(M_{\mathrm{AB}}\) over \(\operatorname{ran}E_0\).

For the logarithmic carry partition, \(B_0\ne0\).

---

# Parte XIV — API Lean proposta

## 50. Princípio de implementação

O repositório novo deve ser independente do repositório histórico. Ele deve depender somente de Lean/Mathlib.

A formalização deve seguir a ordem:

```text
aritmética finita
-> partição admissível
-> espaços de índices
-> operadores no core
-> cotas de norma
-> extensão contínua
-> operador de frame
-> normalização
-> Poisson
-> seções finitas
```

---

## 51. Tipos e definições sugeridas

```lean
/-- Positive integer state index, represented by `n + 1`. -/
abbrev PositiveIndex := ℕ

/-- A base-event pair `(b,n)` with `2 ≤ b` and `b ∣ n`. -/
structure BaseEvent where
  base : ℕ
  number : ℕ
  base_ge_two : 2 ≤ base
  number_pos : 0 < number
  divides : base ∣ number

def positionalDepth (b n : ℕ) : ℕ := ...

def allBaseActivity (b n : ℕ) : ℝ :=
  positionalDepth b n * Real.log b

def allBaseNormalizer (n : ℕ) : ℝ :=
  ∑ b ∈ Finset.Icc 2 n, allBaseActivity b n

def carryCameraWeight (b n : ℕ) : ℝ :=
  if 1 < n ∧ b ∣ n then
    allBaseActivity b n / allBaseNormalizer n
  else 0
```

---

## 52. Partição admissível abstrata

```lean
structure AdmissibleCameraPartition where
  weight : ℕ → ℕ → ℝ
  nonneg : ∀ b n, 0 ≤ weight b n
  support_divides :
    ∀ {b n}, weight b n ≠ 0 → 2 ≤ b ∧ 0 < n ∧ b ∣ n
  sum_eq_one :
    ∀ {n}, 1 < n →
      (∑ b ∈ Finset.Icc 2 n, weight b n) = 1
```

Teoremas:

```lean
theorem carryCameraWeight_admissible :
    AdmissibleCameraPartition

theorem admissible_weight_le_one
    (ω : AdmissibleCameraPartition) :
    ω.weight b n ≤ 1
```

---

## 53. Lemas aritméticos

```lean
theorem positionalDepth_pos_iff_dvd
    (hb : 2 ≤ b) (hn : 0 < n) :
    0 < positionalDepth b n ↔ b ∣ n

theorem allBaseNormalizer_pos
    (hn : 1 < n) :
    0 < allBaseNormalizer n

theorem carryCameraWeight_sum_eq_one
    (hn : 1 < n) :
    ∑ b ∈ Finset.Icc 2 n, carryCameraWeight b n = 1

theorem bulkActivity_le_two_mul_depthOneActivity
    (hn : 1 < n) :
    bulkActivity n ≤ 2 * depthOneActivity n
```

---

## 54. Espaços \(\ell^2\)

Sugestão:

```lean
abbrev StateL2 (𝕜 : Type*) [RCLike 𝕜] :=
  lp (fun _ : PositiveIndex => 𝕜) 2

abbrev ResidualL2 (𝕜 : Type*) [RCLike 𝕜] :=
  lp (fun _ : BaseEvent => 𝕜) 2
```

Criar subtipos:

```lean
def DepthOneEvent := {e : BaseEvent // positionalDepth e.base e.number = 1}
def BulkEvent := {e : BaseEvent // 2 ≤ positionalDepth e.base e.number}
```

---

## 55. Coeficientes de análise

```lean
def carryRatio (b : ℕ) : ℝ := (b : ℝ) ^ (-(1 : ℝ) / 2)

def greenMass
    (ω : AdmissibleCameraPartition) (b n : ℕ) : ℝ :=
  ω.weight b n / b

def residualMass
    (ω : AdmissibleCameraPartition) (b n : ℕ) : ℝ :=
  ω.weight b n * (1 - 1 / b)

def greenStencil
    (b n : ℕ) (f : PositiveIndex → 𝕜) : 𝕜 :=
  f n
    - 2 * carryRatio b * f (n / b)
    + if b^2 ∣ n then (1 / b) * f (n / b^2) else 0
```

Na implementação real, os casts e o índice positivo devem ser tratados por uma API auxiliar, evitando divisões fora do suporte.

---

## 56. Teoremas de norma

```lean
theorem residual_seed_norm_sq_bounds
    (ω : AdmissibleCameraPartition) (f : StateL2 𝕜) :
    (1 / 2 : ℝ) * ‖f‖^2
      ≤ seedResidualNormSq ω f ∧
    seedResidualNormSq ω f ≤ ‖f‖^2

theorem greenAnalysis_norm_sq_le
    (ω : AdmissibleCameraPartition) (f : StateL2 𝕜) :
    ‖greenAnalysis ω f‖^2 ≤ greenBoundConstant * ‖f‖^2

theorem allBasesGreenAnalysis_bounds
    (ω : AdmissibleCameraPartition) (f : StateL2 𝕜) :
    (1 / 2 : ℝ) * ‖f‖^2
      ≤ ‖fullAnalysis ω f‖^2 ∧
    ‖fullAnalysis ω f‖^2
      ≤ fullFrameBound * ‖f‖^2
```

---

## 57. Teoremas de frame e Poisson

```lean
theorem frameOperator_lower :
    (1 / 2 : ℝ) • ContinuousLinearMap.id 𝕜 (StateL2 𝕜)
      ≤ frameOperator ω

theorem frameOperator_upper :
    frameOperator ω
      ≤ fullFrameBound • ContinuousLinearMap.id 𝕜 (StateL2 𝕜)

theorem normalizedAnalysis_isometry :
    Isometry (normalizedAnalysis ω)

theorem normalizedExternal_boundedBelow :
    ∃ c > 0, ∀ f,
      c * ‖f‖ ≤ ‖normalizedExternal ω f‖

theorem normalizedExternal_range_closed :
    IsClosed (LinearMap.range (normalizedExternal ω))

theorem poisson_intertwining :
    poissonOperator ω ∘L normalizedExternal ω
      = normalizedBulk ω

theorem coherentRange_eq_graph :
    LinearMap.range (normalizedAnalysis ω)
      = graphSubspace (poissonOperator ω)
```

---

## 58. Witness de bulk

```lean
theorem carryWeight_two_four :
    carryCameraWeight 2 4 = 1 / 2

theorem rawBulk_nonzero :
    rawBulkAnalysis carryPartition ≠ 0

theorem normalizedBulk_norm_sq_lower :
    1 / (4 * fullFrameBound)
      ≤ ‖normalizedBulk carryPartition‖^2

theorem poisson_nonzero :
    poissonOperator carryPartition ≠ 0
```

---

# Parte XV — Arquitetura do repositório

## 59. Nome recomendado

```text
all-bases-green-frame
```

### Descrição curta

```text
A carry-weighted arithmetic frame on ℓ² built from all positional bases,
with explicit bounds, canonical Parseval normalization, and bounded Poisson
reconstruction of the Green bulk.
```

### Descrição em português

```text
Frame aritmético em ℓ² construído com todas as bases posicionais,
split pitagórico Green–retorno, cotas explícitas, normalização de Parseval
e reconstrução limitada do bulk por um operador de Poisson canônico.
```

---

## 60. Estrutura sugerida

```text
all-bases-green-frame/
├── README.md
├── LICENSE
├── CITATION.cff
├── .zenodo.json
├── lean-toolchain
├── lakefile.toml
├── AllBasesGreenFrame.lean
├── AllBasesGreenFrame/
│   ├── Arithmetic/
│   │   ├── PositionalDepth.lean
│   │   ├── Activity.lean
│   │   ├── AdmissiblePartition.lean
│   │   ├── CarryPartition.lean
│   │   └── DepthOneCharge.lean
│   ├── Hilbert/
│   │   ├── IndexSpaces.lean
│   │   ├── ElementaryAtlas.lean
│   │   ├── PythagoreanSplit.lean
│   │   ├── GreenStencil.lean
│   │   ├── ResidualAnalysis.lean
│   │   ├── GreenBesselBound.lean
│   │   ├── FrameOperator.lean
│   │   ├── CanonicalParseval.lean
│   │   ├── PoissonCompletion.lean
│   │   └── NontrivialBulk.lean
│   ├── Finite/
│   │   ├── Sections.lean
│   │   ├── UniformBounds.lean
│   │   └── StrongConvergence.lean
│   └── PublicAPI.lean
├── python/
│   ├── finite_all_bases_frame.py
│   ├── verify_universal_constants.py
│   ├── verify_poisson_intertwining.py
│   └── compare_cutoffs.py
├── tests/
│   ├── test_partition.py
│   ├── test_green_stencil.py
│   ├── test_frame_bounds.py
│   ├── test_poisson.py
│   └── test_bulk_witness.py
├── artifacts/
│   └── finite_audits/
├── audit/
│   ├── THEOREM_REGISTRY.md
│   ├── CLAIM_LEDGER.md
│   ├── SOURCE_PROVENANCE.md
│   └── SHA256SUMS.txt
└── docs/
    ├── 00_SCOPE.md
    ├── 10_ARITHMETIC_PARTITION.md
    ├── 20_GREEN_ANALYSIS.md
    ├── 30_FRAME_THEOREM.md
    ├── 40_POISSON_COMPLETION.md
    ├── 50_FINITE_SECTIONS.md
    ├── 60_CONSTANT_OPTIMIZATION.md
    └── 70_FUTURE_WEYL_LAYER.md
```

---

# Parte XVI — Ledger de afirmações

## 61. Estados

- `PAPER_PROVED`: prova matemática completa neste documento;
- `FINITE_EXACT`: identidade exata implementada em dimensão finita;
- `NUMERIC_AUDITED`: evidência de máquina, não usada como premissa;
- `LEAN_PENDING`: enunciado ainda não elaborado pelo kernel;
- `KERNEL_CHECKED`: reservado para depois de `lake build --wfail`;
- `FUTURE_LAYER`: não pertence ao teorema inicial.

---

## 62. Claim ledger inicial

| ID | Afirmação | Estado atual |
|---|---|---|
| ABGF-AR-001 | suporte das bases ativas de \(n\) é finito | PAPER_PROVED |
| ABGF-AR-002 | pesos log-depth formam partição de unidade | PAPER_PROVED / FINITE_EXACT |
| ABGF-AR-003 | atividade bulk \(\le2\) atividade depth-one | PAPER_PROVED |
| ABGF-AN-001 | atlas elementar \(A\) é isometria | PAPER_PROVED / FINITE_EXACT |
| ABGF-AN-002 | horizontal de uma base é resolvida pelas verticais restantes | PAPER_PROVED / FINITE_EXACT |
| ABGF-GR-001 | split \(\mu_G+\mu_R=\omega\) | PAPER_PROVED / FINITE_EXACT |
| ABGF-GR-002 | massa residual total \(\ge1/2\) | PAPER_PROVED |
| ABGF-GR-003 | stencil global coincide com a TFVD de torre normalizada | PAPER_PROVED / FINITE_EXACT |
| ABGF-GR-004 | \(\|Gf\|^2\le C_G\|f\|^2\) | PAPER_PROVED |
| ABGF-FR-001 | \(T\) é frame com bounds \(1/2,C_F\) | PAPER_PROVED / LEAN_PENDING |
| ABGF-FR-002 | \(F=T^*T\) é positivo e invertível | PAPER_PROVED / LEAN_PENDING |
| ABGF-FR-003 | \(V=TF^{-1/2}\) é isometria | PAPER_PROVED / FINITE_EXACT / LEAN_PENDING |
| ABGF-PO-001 | \(E_0\) é limitado inferiormente | PAPER_PROVED |
| ABGF-PO-002 | \(\operatorname{ran}E_0\) é fechada | PAPER_PROVED |
| ABGF-PO-003 | \(M_{\mathrm{AB}}E_0=B_0\) | PAPER_PROVED / FINITE_EXACT |
| ABGF-PO-004 | imagem coerente é gráfico de \(M_{\mathrm{AB}}\) | PAPER_PROVED |
| ABGF-BK-001 | bulk canônico é não nulo | PAPER_PROVED / FINITE_EXACT |
| ABGF-BK-002 | cota explícita \(\|B_0\|^2\ge1/(4C_F)\) | PAPER_PROVED |
| ABGF-FS-001 | seções finitas têm bounds uniformes | PAPER_PROVED |
| ABGF-FS-002 | \(T_N\to T\) fortemente | PAPER_PROVED |
| ABGF-FS-003 | \(V_N\to V\) fortemente | PAPER_ARGUMENT / LEAN_PENDING |
| ABGF-FS-004 | \(M_N\to M_{\mathrm{AB}}\) fortemente | FUTURE_LAYER |
| ABGF-WEYL-001 | família de Weyl por Schur do gerador \(\log n\) | FUTURE_LAYER |

---

# Parte XVII — Estratégia de formalização

## 63. Fase 1 — núcleo aritmético

Entregas:

1. `positionalDepth`;
2. suporte finito;
3. normalizador positivo;
4. pesos de carry;
5. partição de unidade;
6. lema depth-one de \(1/3\).

Critério de conclusão:

```text
lake build --wfail AllBasesGreenFrame.Arithmetic
```

---

## 64. Fase 2 — operadores no core

Entregas:

1. espaços de índice;
2. vetores residual e Green;
3. igualdade com o stencil de torre;
4. análise elementar de Parseval;
5. split pitagórico.

O operador Green deve ser definido primeiro no subespaço denso de sequências finitamente suportadas.

---

## 65. Fase 3 — bound Green

Esta é a primeira peça analítica central.

Formalizar separadamente:

```text
current-coordinate contribution
parent contribution
grandparent contribution
```

e depois somar.

Evitar qualquer biblioteca de funções especiais. As únicas entradas são a somabilidade das séries reais

\[
\sum_{b\ge2}b^{-2},
\qquad
\sum_{b\ge2}b^{-3}.
\]

A constante pode permanecer definida pelas próprias séries.

---

## 66. Fase 4 — extensão e frame

1. estender o operador do core por continuidade;
2. provar as cotas;
3. definir \(F=T^*T\);
4. provar positividade forte;
5. construir \(F^{-1/2}\);
6. provar \(V^*V=I\).

Esta fase fecha o teorema que dá nome ao repositório.

---

## 67. Fase 5 — Poisson

1. decompor \(V=(E_0,B_0)\);
2. provar \(E_0^*E_0\ge\alpha I\);
3. construir a inversa à esquerda;
4. provar que \(\Pi_E\) é projeção ortogonal;
5. definir \(M_{\mathrm{AB}}\);
6. provar o intertwining;
7. provar a descrição por gráfico;
8. provar o witness \((2,4)\).

---

## 68. Fase 6 — seções finitas

1. definir \(T_N\);
2. provar bounds uniformes;
3. importar o algoritmo Python como auditoria independente;
4. provar convergência forte;
5. comparar certificados finitos com a teoria.

---

# Parte XVIII — Plano de testes

## 69. Testes aritméticos

- `sum_b omega_b(n) = 1` para \(2\le n\le N\);
- suporte somente em divisores;
- \(\omega_2(4)=1/2\);
- depth-one share \(\ge1/3\);
- comparação com o subatlas primo.

---

## 70. Testes do stencil

Para cada torre:

- comparar a fórmula global com a matriz TFVD local;
- profundidade \(1\): dois termos;
- profundidade \(\ge2\): três termos;
- bases primas e compostas;
- casos \(b=2,3,4,6,9\).

---

## 71. Testes de frame

- confirmar \(T_N^*T_N>0\);
- comparar autovalores com \(1/2\) e \(C_F\);
- confirmar `normalized_isometry_error`;
- confirmar conservação

\[
\|f\|^2=\|E_0f\|^2+\|B_0f\|^2;
\]

- testar vetores aleatórios e vetores de base.

---

## 72. Testes de Poisson

- \(M_NE_{0,N}=B_{0,N}\);
- \(\Pi_E^2=\Pi_E\);
- \(\Pi_E^*=\Pi_E\);
- \(P_NE_{0,N}=V_N\);
- invariância sob mudança ortogonal da base redundante do codomínio;
- witness bulk \(e_4\).

---

# Parte XIX — Camada espectral futura

## 73. Gerador logarítmico

Depois do frame estar fechado, defina em \(H\)

\[
(Lf)(n)=\log n\,f(n)
\]

com domínio natural

\[
D(L)=
\left\{
f\in H:
\sum_n(\log n)^2|f(n)|^2<\infty
\right\}.
\]

\(L\) é autoadjunto por ser um operador diagonal real.

---

## 74. Transporte ao atlas de Parseval

A isometria \(V\) leva \(L\) ao subespaço coerente:

\[
H_{\mathrm{coh}}
=
VLV^*|_{\operatorname{ran}V}.
\]

Esse operador é autoadjunto em \(\operatorname{ran}V\).

O problema seguinte é expressá-lo na decomposição

\[
K_{\mathrm{ext}}\oplus K_{\mathrm{bulk}}
\]

e estudar seus blocos.

---

## 75. Gamma e Weyl

Se um problema de bordo fixo for definido com domínio correto, a família de Poisson espectral terá a forma

\[
\gamma(z)
=
(z-H_{BB})^{-1}H_{BE}
\]

e a função de Weyl/Schur,

\[
W(z)
=
z-H_{EE}
-H_{EB}(z-H_{BB})^{-1}H_{BE}.
\]

### Guardrail

O operador fixo \(M_{\mathrm{AB}}\) deste documento é uma reconstrução cinemática external-to-bulk. Ele é a infraestrutura para uma futura família de Weyl, mas ainda não é essa família.

A camada espectral só deve entrar depois que forem provados:

1. domínio denso;
2. blocos fechados;
3. conjunto resolvente;
4. relação de bordo;
5. maximalidade/autoadjunticidade.

---

# Parte XX — Proveniência do material existente

## 76. Fontes computacionais principais

Repositório histórico:

```text
thiagomassensini/carry-lab
```

Arquivos de origem:

```text
scripts/native_carry_conservative_all_bases_atlas_lab.py
scripts/native_carry_quadratic_weighted_green_atlas_lab.py
scripts/native_carry_pythagorean_green_measure_lab.py
scripts/native_carry_multibase_weyl_operator_lab.py
scripts/native_carry_global_boundary_triple_lab.py
scripts/native_carry_minimal_multibase_characteristic_lab.py
```

Artefato principal:

```text
artifacts/native_carry_pythagorean_green_measure/
  pythagorean_green_measure_audit.json
```

O script do frame pitagórico registra:

- \(E_{\mathrm{ext}}^*E_{\mathrm{ext}}\ge\frac12I\);
- bound universal do Green;
- normalização \(V=T(T^*T)^{-1/2}\);
- Poisson finito;
- witness uniforme de bulk.

---

## 77. Fontes formais relacionadas

Repositório:

```text
thiagomassensini/primos
```

Peças reutilizáveis como referência conceitual:

```text
CPFormal/Logic/StructuralPersistence.lean
CPFormal/Analytic/CpTfvdSeededFiniteBesselConservation.lean
CPFormal/Analytic/CpFiniteTfvdAngularGreenIntertwiner.lean
```

Essas peças já formalizam:

- persistência de readout sob mudança de apresentação;
- conservação finita Bessel/TFVD;
- necessidade informacional de um porto dormente;
- separação entre energia visível e residual.

O novo repositório não deve depender do grafo inteiro de `primos`. A prova do frame deve ser reescrita como biblioteca autônoma, com documentação de proveniência.

---

## 78. Bloqueio de fonte sugerido

Registrar em `audit/SOURCE_PROVENANCE.md`:

```text
carry-lab source snapshot:
  commit 8ae5c0b9c0c5aa446417f1b179c82447e91f9913

primary historical implementation:
  commit 2d7f30c102e12681fc0860fb216055426224f3b8
```

E os blobs centrais:

```text
native_carry_conservative_all_bases_atlas_lab.py
  660f71f67e6337c8730694f25d968def9195461f

native_carry_pythagorean_green_measure_lab.py
  04b5b79e12c6deffdb11fc4012f428d6911f5b52

pythagorean_green_measure_audit.json
  2772e1a91e81f918e7337699f518fa9e093f20a9
```

Verificar novamente esses identificadores no momento da criação do repositório.

---

# Parte XXI — Decisões editoriais

## 79. Vocabulário canônico

Usar:

- **base** para o parâmetro posicional \(b\);
- **evento** para o par \((b,n)\);
- **profundidade** para \(k_b(n)\);
- **partição de câmeras** para \(\omega_b(n)\);
- **canal Green** para \(\mu_G\);
- **canal residual/retorno** para \(\mu_R\);
- **externo** para seed + residual + Green depth-one;
- **bulk** para Green depth \(\ge2\);
- **análise completa** para \(T\);
- **análise normalizada** para \(V\);
- **compatibilidade externa** para \(\operatorname{ran}E_0\);
- **Poisson all-bases** para \(M_{\mathrm{AB}}\).

Evitar no núcleo:

- linguagem de zeros;
- funções especiais;
- nomes de conjecturas;
- “calibração” posterior;
- tratar evidência finita como limite;
- chamar \(M_{\mathrm{AB}}\) de função de Weyl antes da construção espectral.

---

## 80. Política de prova

Cada afirmação deve ser classificada como:

```text
DEFINITION
FINITE_IDENTITY
PAPER_PROVED
KERNEL_CHECKED
NUMERICAL_AUDIT
OPEN_EXTENSION
```

Nenhum resultado passa para `KERNEL_CHECKED` sem:

```bash
lake build --wfail
```

e auditoria contra:

```text
sorry
admit
axiom local
unsafe
```

---

# Parte XXII — Ordem recomendada de execução

## 81. Primeiro milestone

Publicar um repositório verde contendo:

1. partição admissível abstrata;
2. pesos canônicos de carry;
3. split pitagórico;
4. operadores finitos;
5. auditoria Python limpa;
6. enunciado do teorema infinito como `LEAN_STATEMENT`, ainda sem instância se necessário.

Tag sugerida:

```text
v0.1.0 — finite arithmetic partition and Green frame model
```

---

## 82. Segundo milestone

Fechar no Lean:

\[
\|Gf\|^2\le C_G\|f\|^2.
\]

Tag:

```text
v0.2.0 — universal Green Bessel bound
```

---

## 83. Terceiro milestone

Fechar:

\[
\frac12I\le T^*T\le C_FI
\]

e

\[
V^*V=I.
\]

Tag:

```text
v1.0.0 — All-Bases Green Frame Theorem
```

Este é o primeiro checkpoint matemático publicável com o nome do teorema.

---

## 84. Quarto milestone

Fechar:

\[
M_{\mathrm{AB}}E_0=B_0
\]

e a descrição por gráfico.

Tag:

```text
v1.1.0 — canonical Poisson completion
```

---

## 85. Quinto milestone

Formalizar seções finitas e convergência forte.

Tag:

```text
v1.2.0 — finite-section convergence
```

Somente depois disso iniciar a camada espectral em branch separada.

---

# Parte XXIII — Conclusão

O objeto matemático que deve ser promovido ao repositório exclusivo não é um scanner, uma câmera específica ou uma rota de zeros.

É a seguinte estrutura:

\[
\boxed{
\begin{aligned}
&\text{cada inteiro é distribuído entre suas bases ativas};\\
&\text{cada massa de câmera se divide em Green e retorno};\\
&\text{os stencils e os retornos formam um frame de }\ell^2;\\
&\text{o frame possui normalização canônica de Parseval};\\
&\text{o setor externo é completo e tem imagem fechada};\\
&\text{o bulk coerente é reconstruído por um Poisson limitado};\\
&\text{o bulk permanece não trivial.}
\end{aligned}
}
\]

O resultado é independente de conjecturas e pode ser usado como ferramenta de:

- análise multirresolução aritmética;
- frames redundantes;
- decomposição external–bulk;
- reconstrução de Green;
- teoria de observabilidade;
- sistemas passivos;
- aproximações por cutoff;
- construção futura de famílias de Weyl.

A frase central do projeto pode ser:

> **Todas as bases observam o mesmo estado por canais redundantes; o split de carry transforma essa redundância em um frame conservativo, e a normalização canônica transforma o bulk em uma função limitada dos portos externos.**

