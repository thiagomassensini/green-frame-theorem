---
title: "Teorema da Ponte Ortogonal Carry–Fase"
subtitle: "Memória completa da suspeita sobre Newton à identidade exata"
date: 2026-08-01
status: "Identidade finita formalizada em Lean; fechamento estrutural da ponte global em organização"
tags:
  - carry-geometry
  - operador-nativo
  - C2
  - multibase
  - ponte-ortogonal
  - Lean4
  - memoria-de-pesquisa
---

# Teorema da Ponte Ortogonal Carry–Fase

## Memória completa da suspeita sobre Newton à identidade exata

> A compressão em `sigma` e o giro em `t` não são duas engrenagens independentes. No operador nativo real, são a mesma variação vista através de uma rotação ortogonal exata de 90 graus.

A identidade central é:

$$
\boxed{
\partial_t R_{c,M}(\sigma,t)
=
\mathcal J\,\partial_\sigma R_{c,M}(\sigma,t)
}
$$

com

$$
\mathcal J(x,y)=(-y,x),
\qquad
\mathcal J^2=-I,
\qquad
\mathcal J^{\mathsf T}\mathcal J=I.
$$

Esta memória registra todo o caminho que levou até essa ponte: o experimento off-axis, a leitura inicialmente equivocada do Newton, a lembrança do protocolo correto dos operadores C2, o resultado perfeito demais do Jacobiano, a derivação algébrica da identidade, suas consequências geométricas e o enunciado estrutural que deve conectar a versão finita ao operador global.

O objetivo deste documento não é apenas guardar a fórmula final. É preservar a sequência lógica da descoberta, inclusive o erro de interpretação que revelou a estrutura correta.

---

# 1. Contexto da investigação

A pergunta que motivou os testes era, em essência:

> Um zero do operador nativo pode permanecer fora de `sigma = 1/2`, ou os aparentes deslocamentos off-axis são apenas defeitos do cutoff finito?

O agente iniciou uma bateria de experimentos com o operador nativo real, sem depender do plano complexo. Foram misturadas três camadas diferentes:

1. testes numéricos com cutoff finito;
2. análise local do Jacobiano;
3. compilação de módulos formais no Lean.

Essa mistura produziu uma narrativa aparentemente forte: zeros truncados ligeiramente fora do eixo convergiam para `sigma = 1/2`; câmeras diferentes pareciam colapsar para o mesmo ponto; e um teste do Jacobiano parecia revelar uma “rigidez transversal” impedindo que o zero saísse do eixo.

A parte decisiva foi perceber que a última interpretação estava errada — e que o resultado numérico perfeito escondia uma identidade exata muito mais importante.

---

# 2. O operador real usado nos testes

O código avalia canais do operador na forma vetorial real

$$
R_{c,M}(\sigma,t)
=
\sum_{j\in I_{c,M}}
w_j e^{-\sigma L_j}
\begin{pmatrix}
\cos(-tL_j)\\
\sin(-tL_j)
\end{pmatrix},
$$

onde:

- `c` é a câmera ou base;
- `M` é o cutoff;
- `L_j` representa os logaritmos associados às entradas da câmera;
- `w_j` inclui os pesos dos canais, como semente, esquerda, centro e direita;
- no bracket usado no script aparecem pesos do tipo `1, 1, -2, 1`;
- `sigma` controla a compressão de amplitude;
- `t` controla o giro de fase;
- o operador assume valores diretamente em `R²`.

No código da varredura, a estrutura era essencialmente:

```python
amp = np.exp(-sigma * L)
ang = -t * L
Rx += w * (amp * np.cos(ang)).sum()
Ry += w * (amp * np.sin(ang)).sum()
```

A forma real em duas coordenadas é suficiente para toda a identidade. Não é necessário invocar o plano complexo para enunciá-la, prová-la ou interpretá-la geometricamente.

---

# 3. Primeiro experimento: Newton livre em `(sigma,t)`

O agente começou sobre um vale localizado no eixo `sigma = 1/2` e depois liberou um Newton bidimensional para mover simultaneamente `sigma` e `t`.

O algoritmo buscava resolver exatamente, para cada cutoff,

$$
R_{c,M}(\sigma,t)=0.
$$

## 3.1 Resultados da câmera 2

Foram registrados:

| cutoff `M` | `sigma` encontrado | `delta = sigma - 1/2` | `t` | `||R||` |
|---:|---:|---:|---:|---:|
| 1.024 | 0.499984495867 | -1.5504e-05 | 14.134731464849 | 4.13e-16 |
| 4.096 | 0.499999101608 | -8.9839e-07 | 14.134727033105 | 6.90e-16 |
| 16.384 | 0.500000077503 | +7.7503e-08 | 14.134725391769 | 6.75e-16 |
| 65.536 | 0.500000028312 | +2.8312e-08 | 14.134725158142 | 1.18e-16 |
| 262.144 | 0.500000003992 | +3.9917e-09 | 14.134725140842 | 3.90e-16 |
| 1.048.576 | 0.500000000291 | +2.9099e-10 | 14.134725141314 | 1.44e-16 |

O deslocamento `delta` diminuía à medida que o cutoff crescia, enquanto `t` convergia para aproximadamente

$$
14.13472514\ldots
$$

## 3.2 Resultados da câmera 3

Também foram registrados:

| cutoff `M` | `sigma` encontrado | `delta` | `t` | `||R||` |
|---:|---:|---:|---:|---:|
| 1.024 | 0.500008447308 | +8.4473e-06 | 14.134734779263 | 8.93e-16 |
| 4.096 | 0.500001593022 | +1.5930e-06 | 14.134725319329 | 1.89e-15 |
| 16.384 | 0.500000161565 | +1.6157e-07 | 14.134725023188 | 1.54e-15 |
| 65.536 | 0.500000004799 | +4.7990e-09 | 14.134725117149 | 1.32e-15 |

A primeira leitura foi:

> Cada câmera possui um zero finito ligeiramente diferente, mas todos colapsam para `sigma = 1/2` quando `M` cresce.

Essa leitura contém uma observação numérica verdadeira — os pontos devolvidos pelo Newton convergem para o eixo — mas atribui ao Newton um significado estrutural que ele não possui nesses operadores.

---

# 4. Por que o Newton era a ferramenta errada para interpretar os zeros C2

A correção decisiva veio da memória dos experimentos anteriores da teoria C2.

Nos operadores nativos, o objeto depende do cutoff. O fenômeno útil já observado era:

$$
M\uparrow
\quad\Longrightarrow\quad
\begin{cases}
\text{o vale nativo aprofunda},\\
\text{o mínimo converge em posição},\\
\text{a concordância com os zeros de referência melhora},\\
\text{a concordância entre câmeras melhora}.
\end{cases}
$$

Esse comportamento havia sido obtido sem Newton, por meio de:

- operador nativo real;
- câmera par, ímpar, prima ou composta;
- cutoff crescente;
- grid fino;
- localização direta dos mínimos;
- cálculo intervalar;
- precisão superior ao limite prático do `float64` em testes anteriores.

O número exato de casas obtido pelo cálculo intervalar não aparece no log usado nesta memória e, por isso, não é inventado aqui. O fato estrutural importante é que o protocolo sem Newton já havia ultrapassado `float64` e mostrado melhora sistemática quando o cutoff aumentava.

## 4.1 O defeito de cutoff

Escreva o operador truncado como

$$
R_{c,M}=R_{c,\infty}+E_{c,M},
$$

onde `E_{c,M}` é o defeito introduzido pelo cutoff.

Mesmo que o operador limite tenha um zero estrutural em

$$
R_{c,\infty}\left(\frac12,t_0\right)=0,
$$

o operador truncado geralmente satisfaz

$$
R_{c,M}\left(\frac12,t_0\right)=E_{c,M}\neq0.
$$

Quando o Newton pode mover `sigma` e `t`, ele procura uma correção

$$
(\delta\sigma_M,\delta t_M)
$$

que cancele exatamente o defeito finito:

$$
R_{c,M}
\left(
\frac12+\delta\sigma_M,
 t_0+\delta t_M
\right)=0.
$$

Na primeira ordem,

$$
D R_{c,M}
\begin{pmatrix}
\delta\sigma_M\\
\delta t_M
\end{pmatrix}
\approx
-E_{c,M},
$$

portanto

$$
\begin{pmatrix}
\delta\sigma_M\\
\delta t_M
\end{pmatrix}
\approx
-igl(DR_{c,M}\bigr)^{-1}E_{c,M}.
$$

Assim, o Newton pode reduzir o resíduo algébrico para a escala de `1e-16` enquanto desloca a posição espectral para absorver o erro do cutoff.

## 4.2 A distinção essencial

O Newton encontra com alta precisão:

> o zero exato do operador truncado daquele cutoff.

Mas isso não é automaticamente:

> a melhor aproximação do zero estrutural do operador limite.

Para o operador C2, já havia evidência de que o caminho mais fiel era observar o vale nativo se aprofundando e convergindo com `M`, sem permitir que um refinador bidimensional transformasse o defeito finito em deslocamento das coordenadas.

Uma formulação precisa é:

> Newton melhora a satisfação da equação truncada `R_{c,M}=0`, mas pode piorar a localização do zero estrutural que emerge no limite `M -> infinito`.

## 4.3 Consequência para a leitura multibase

A interpretação inicial dizia que “uma câmera sozinha aceitaria um zero fora do eixo” e que a sobredeterminação multibase arrastaria a interseção para `1/2`.

A leitura mais prudente é:

1. cada câmera possui seu próprio defeito de cutoff `E_{c,M}`;
2. o Newton converte esse defeito em um deslocamento `delta sigma_{c,M}`;
3. quando `M` cresce, `E_{c,M}` diminui;
4. os deslocamentos produzidos pelo Newton também diminuem;
5. isso explica o aparente colapso sem precisar postular zeros estruturais off-axis em cada câmera.

Logo, os dados continuam valiosos como diagnóstico do cutoff, mas não demonstram por si sós um mecanismo de sobredeterminação global.

---

# 5. Varredura da paisagem transversal sem Newton

Outro teste fixou vários valores de `sigma` e, para cada um, procurou sobre uma grade de `t` o menor valor de `||R||` na janela próxima de `14.1347`.

Para a câmera 2, com `M = 16384`, obteve-se:

| `sigma` | `min_t ||R(sigma,t)||` |
|---:|---:|
| 0.200 | 1.783e-01 |
| 0.225 | 1.877e-01 |
| 0.250 | 1.936e-01 |
| 0.275 | 1.810e-01 |
| 0.300 | 1.627e-01 |
| 0.325 | 1.432e-01 |
| 0.350 | 1.230e-01 |
| 0.375 | 1.025e-01 |
| 0.400 | 8.184e-02 |
| 0.425 | 6.120e-02 |
| 0.450 | 4.064e-02 |
| 0.475 | 2.023e-02 |
| 0.500 | 1.004e-04 |
| 0.525 | 2.002e-02 |
| 0.550 | 3.980e-02 |
| 0.575 | 5.935e-02 |
| 0.600 | 7.864e-02 |
| 0.625 | 9.769e-02 |
| 0.650 | 1.165e-01 |
| 0.675 | 1.350e-01 |
| 0.700 | 1.534e-01 |
| 0.725 | 1.714e-01 |
| 0.750 | 1.893e-01 |
| 0.775 | 2.069e-01 |
| 0.800 | 2.243e-01 |

Esse teste mostra um vale transversal acentuado em torno de `sigma = 1/2`.

O valor `1.004e-04` no eixo não contradiz resíduos menores obtidos em outros testes. A busca usou apenas uma grade de 4.000 pontos em `t`; ela não precisava atingir exatamente a posição do mínimo.

Este tipo de varredura é mais compatível com o protocolo nativo porque não permite que Newton ajuste `sigma` para zerar o defeito do cutoff.

Ainda assim, uma única varredura finita é evidência numérica, não uma prova do operador limite.

---

# 6. O script da “rigidez transversal”

O agente então construiu o seguinte experimento:

1. fixar inicialmente `sigma = 1/2`;
2. localizar aproximadamente um vale em `t`;
3. executar Newton em duas dimensões;
4. obter um zero truncado `(sigma*,t*)`;
5. calcular o Jacobiano nesse ponto;
6. comparar `dR/dsigma` e `dR/dt`;
7. medir uma componente chamada `k_perp`.

O núcleo era:

```python
r = P.newton_2d(model, 0.5, tv, 60)
sig, t = r['sigma'], r['t']
R, J = P.resultant_and_jacobian(model, sig, t)

gs = J[:, 0]  # dR/dsigma
gt = J[:, 1]  # dR/dt

ns = np.hypot(*gs)
nt = np.hypot(*gt)

cosang = np.dot(gs, gt) / (ns * nt)
ang = acos(cosang)

ghat = gt / nt
perp = gs - np.dot(gs, ghat) * ghat
kperp = np.hypot(*perp)
```

A interpretação pretendida era:

> Se `k_perp > 0`, sair em `sigma` produz uma componente que nenhum ajuste em `t` consegue cancelar.

Essa afirmação é localmente correta como leitura linear, mas o resultado do teste revelou algo muito mais forte — e também mostrou que a interpretação “especial do eixo” estava errada.

---

# 7. O resultado perfeito demais

A execução devolveu:

```text
Geometria local do zero (camera 2): eixo amplitude vs fase
 M | |dR/dsigma| | |dR/dt| | angulo(graus) | k_perp | k_perp/|dR/dt|
     4096 | 8.0507e-01 | 8.0507e-01 | 90.0000 | 8.0507e-01 | 1.0000e+00
    16384 | 8.0508e-01 | 8.0508e-01 | 90.0000 | 8.0508e-01 | 1.0000e+00
    65536 | 8.0508e-01 | 8.0508e-01 | 90.0000 | 8.0508e-01 | 1.0000e+00
   262144 | 8.0508e-01 | 8.0508e-01 | 90.0000 | 8.0508e-01 | 1.0000e+00
```

Os dados exibiam simultaneamente:

$$
\|\partial_\sigma R\|=\|\partial_tR\|,
$$

$$
\angle(\partial_\sigma R,\partial_tR)=90^\circ,
$$

$$
k_\perp=\|\partial_\sigma R\|,
$$

$$
\frac{k_\perp}{\|\partial_tR\|}=1.
$$

A perfeição e a repetição desses números para todos os cutoffs eram a pista principal:

> Isto não era um fenômeno numérico emergente do zero. Era uma identidade algébrica presente na definição do operador.

O Newton não havia descoberto a ortogonalidade. Ele apenas avaliara uma identidade universal num ponto escolhido por Newton.

---

# 8. Derivação exata da identidade

Considere um único termo do operador:

$$
v_j(\sigma,t)
=
w_j e^{-\sigma L_j}
\begin{pmatrix}
\cos(-tL_j)\\
\sin(-tL_j)
\end{pmatrix}.
$$

## 8.1 Derivada em `sigma`

Como

$$
\partial_\sigma e^{-\sigma L_j}
=
-L_j e^{-\sigma L_j},
$$

temos

$$
\partial_\sigma v_j
=
-w_jL_j e^{-\sigma L_j}
\begin{pmatrix}
\cos(-tL_j)\\
\sin(-tL_j)
\end{pmatrix}.
$$

## 8.2 Derivada em `t`

Usando

$$
\frac{d}{dt}\cos(-tL_j)=L_j\sin(-tL_j),
$$

$$
\frac{d}{dt}\sin(-tL_j)=-L_j\cos(-tL_j),
$$

obtemos

$$
\partial_t v_j
=
w_jL_j e^{-\sigma L_j}
\begin{pmatrix}
\sin(-tL_j)\\
-\cos(-tL_j)
\end{pmatrix}.
$$

## 8.3 A rotação ortogonal

Defina

$$
\mathcal J
\begin{pmatrix}
x\\y
\end{pmatrix}
=
\begin{pmatrix}
-y\\x
\end{pmatrix}.
$$

Aplicando `J` à derivada em `sigma`:

$$
\mathcal J\,\partial_\sigma v_j
=
\mathcal J
\left[
-w_jL_j e^{-\sigma L_j}
\begin{pmatrix}
\cos(-tL_j)\\
\sin(-tL_j)
\end{pmatrix}
\right],
$$

portanto

$$
\mathcal J\,\partial_\sigma v_j
=
w_jL_j e^{-\sigma L_j}
\begin{pmatrix}
\sin(-tL_j)\\
-\cos(-tL_j)
\end{pmatrix}.
$$

Logo,

$$
\boxed{
\partial_t v_j
=
\mathcal J\,\partial_\sigma v_j
}
$$

termo por termo.

Como o operador é uma soma linear dos termos, com quaisquer pesos reais `w_j`, segue imediatamente:

$$
\boxed{
\partial_t R_{c,M}(\sigma,t)
=
\mathcal J\,\partial_\sigma R_{c,M}(\sigma,t)
}
$$

para qualquer:

- câmera `c`;
- cutoff `M`;
- valor de `sigma`;
- valor de `t`;
- escolha finita de canais e pesos compatível com essa forma;
- ponto que seja zero ou não seja zero.

Essa identidade é exata no operador truncado. Ela não depende de convergência numérica, Newton, localização de mínimos, linha crítica ou escolha particular de câmera.

---

# 9. O Teorema da Ponte Ortogonal Carry–Fase

## 9.1 Enunciado finito

**Teorema da Ponte Ortogonal Carry–Fase, versão finita.**

Seja

$$
R_{c,M}:\mathbb R^2\to\mathbb R^2
$$

o operador nativo real de uma câmera `c`, com cutoff finito `M`, cuja dependência em amplitude e fase é dada por termos

$$
e^{-\sigma L_j}
\begin{pmatrix}
\cos(-tL_j)\\
\sin(-tL_j)
\end{pmatrix}.
$$

Então, em todo ponto `(sigma,t)`,

$$
\boxed{
\partial_t R_{c,M}
=
\mathcal J\,\partial_\sigma R_{c,M}
}
$$

onde `J` é a rotação ortogonal de 90 graus

$$
\mathcal J(x,y)=(-y,x).
$$

## 9.2 Significado estrutural

A derivada em `sigma` mede como a compressão altera radialmente cada componente:

$$
\partial_\sigma e^{-\sigma L}
=-L e^{-\sigma L}.
$$

A derivada em `t` mede como a fase gira cada componente:

$$
\partial_t
\begin{pmatrix}
\cos(-tL)\\
\sin(-tL)
\end{pmatrix}
=
L
\begin{pmatrix}
\sin(-tL)\\
-\cos(-tL)
\end{pmatrix}.
$$

O mesmo fator `L` aparece nas duas variações. O que distingue uma da outra é exatamente a rotação `J`.

Portanto:

$$
\boxed{
\text{variação de fase}
=
\text{rotação ortogonal da variação de compressão}
}
$$

ou, na linguagem da pesquisa:

$$
\boxed{
\text{compressão do carry}
\overset{\mathcal J}{\longleftrightarrow}
\text{giro de fase}
}
$$

Essa é a ponte geométrica.

---

# 10. Consequências exatas da ponte

Defina

$$
u_{c,M}=\partial_\sigma R_{c,M}.
$$

Então

$$
\partial_tR_{c,M}=\mathcal Ju_{c,M}.
$$

O Jacobiano, com as colunas ordenadas por `(sigma,t)`, é

$$
D R_{c,M}
=
\begin{bmatrix}
u_{c,M} & \mathcal Ju_{c,M}
\end{bmatrix}.
$$

Se

$$
u_{c,M}=
\begin{pmatrix}
a\\b
\end{pmatrix},
$$

então

$$
D R_{c,M}
=
\begin{pmatrix}
a & -b\\
b & a
\end{pmatrix}.
$$

## 10.1 Ortogonalidade

Como toda rotação de 90 graus envia um vetor para sua direção ortogonal,

$$
\boxed{
\left\langle
\partial_\sigma R_{c,M},
\partial_tR_{c,M}
\right\rangle
=0
}
$$

em todo ponto.

## 10.2 Igualdade das normas

Como `J` é ortogonal,

$$
\boxed{
\|\partial_tR_{c,M}\|
=
\|\partial_\sigma R_{c,M}\|
}
$$

em todo ponto.

## 10.3 Jacobiano conforme

Temos

$$
\boxed{
(DR_{c,M})^{\mathsf T}DR_{c,M}
=
\|\partial_\sigma R_{c,M}\|^2 I
}
$$

Logo, o diferencial local é uma dilatação uniforme combinada com uma rotação. Não há cisalhamento infinitesimal nem uma direção local privilegiada entre os eixos `sigma` e `t`.

## 10.4 Determinante

A forma matricial fornece

$$
\boxed{
\det(DR_{c,M})
=
a^2+b^2
=
\|\partial_\sigma R_{c,M}\|^2
}
$$

Assim,

$$
\det(DR_{c,M})>0
$$

sempre que a derivada não for nula.

## 10.5 Valores singulares e condicionamento geométrico

Os dois valores singulares são iguais:

$$
\boxed{
s_{\min}(DR_{c,M})
=
s_{\max}(DR_{c,M})
=
\|\partial_\sigma R_{c,M}\|
}
$$

Quando a derivada é não nula,

$$
\boxed{
\kappa_2(DR_{c,M})=1
}
$$

Portanto, o Jacobiano não possui anisotropia infinitesimal. Ele é perfeitamente condicionado quanto à razão entre suas direções principais, embora sua magnitude absoluta possa ser pequena ou grande.

## 10.6 Energia infinitesimal

Para uma pequena variação

$$
h=
\begin{pmatrix}
d\sigma\\dt
\end{pmatrix},
$$

temos

$$
DR_{c,M}h
=
u_{c,M}
 d\sigma
+
\mathcal Ju_{c,M}
 dt.
$$

Pela ortogonalidade e igualdade de normas,

$$
\boxed{
\|DR_{c,M}h\|^2
=
\|u_{c,M}\|^2
\left((d\sigma)^2+(dt)^2\right)
}
$$

Esta é uma identidade de conservação local: o plano dos parâmetros é transportado sem distorção angular, apenas por uma escala comum.

## 10.7 A quantidade `k_perp`

No script,

$$
k_\perp
=
\left\|
\partial_\sigma R
-
\operatorname{proj}_{\partial_tR}
(\partial_\sigma R)
\right\|.
$$

Como as derivadas são exatamente ortogonais,

$$
\operatorname{proj}_{\partial_tR}
(\partial_\sigma R)=0.
$$

Logo,

$$
\boxed{
k_\perp=\|\partial_\sigma R\|}
$$

E, pela igualdade das normas,

$$
\boxed{
\frac{k_\perp}{\|\partial_tR\|}=1
}
$$

sempre que as derivadas forem não nulas.

Isso explica diretamente os valores `90.0000` e `1.0000` do experimento.

---

# 11. O que o experimento realmente descobriu

A interpretação inicial era:

> O Jacobiano revelou uma rigidez transversal especial do zero no eixo crítico.

A leitura correta é:

> O Jacobiano revelou numericamente uma identidade ortogonal universal da parametrização do operador.

A identidade vale:

- no eixo e fora dele;
- no zero e fora do zero;
- para cutoff pequeno ou grande;
- em qualquer câmera compatível;
- antes de qualquer passagem ao limite.

Portanto, o teste não seleciona `sigma = 1/2`.

Ele prova outra coisa, estruturalmente muito mais limpa:

> compressão e fase são coordenadas infinitesimalmente conjugadas por uma rotação exata.

O número aproximadamente estável

$$
0.80508
$$

é a magnitude local das derivadas no ponto escolhido. A igualdade das duas magnitudes, o ângulo de 90 graus e a razão unitária são identidades. A eventual convergência do valor `0.80508` com `M` é uma questão adicional e pode conter informação analítica real sobre o limite do gradiente naquele ponto.

---

# 12. O que a identidade não prova sozinha

É essencial preservar a fronteira lógica.

A Ponte Ortogonal não prova, isoladamente:

1. que todos os zeros estão em `sigma = 1/2`;
2. que não existem zeros isolados fora do eixo;
3. que a linha crítica é selecionada apenas pela ortogonalidade;
4. que o operador infinito é diferenciável sem hipóteses adicionais;
5. que derivada e limite podem ser trocados automaticamente;
6. que o valor `0.80508` possui um limite não nulo;
7. que o Newton fornece a melhor aproximação dos zeros nativos;
8. que o colapso multibase observado numericamente é, sozinho, um teorema de sobredeterminação.

A seleção de `sigma = 1/2` deve vir da estrutura de conservação, balanceamento e rigidez do carry já formalizada na teoria.

A ponte explica como as duas coordenadas do operador se conectam geometricamente. Ela não substitui o teorema de confinamento; ela o ilumina e fornece o mecanismo diferencial que faltava.

---

# 13. A ponte e o teorema de confinamento

O encadeamento conceitual desejado é:

## 13.1 A estrutura do carry seleciona o eixo

A conservação quadrática e a compatibilidade de escala selecionam

$$
\sigma=\frac12.
$$

Na formulação já usada na pesquisa, o zero nativo real satisfaz uma caracterização do tipo

$$
IsNativeCarryRealOperatorZero(c,\sigma,t)
\iff
\left(
\sigma=\frac12
\right)
\land
IsNativeCarryRealOperatorResonance(c,t).
$$

## 13.2 A ponte conecta amplitude e fase

Uma vez definido o operador, temos

$$
\partial_tR_c
=
\mathcal J\partial_\sigma R_c.
$$

Assim, a variação na coordenada de fase não é um mecanismo externo ou decorativo. Ela é a imagem ortogonal da variação de compressão.

## 13.3 O fechamento geométrico

No ponto crítico, o Jacobiano possui a forma

$$
DR_c
=
\begin{bmatrix}
u_c & \mathcal Ju_c
\end{bmatrix},
$$

com

$$
(DR_c)^{\mathsf T}DR_c
=
\|u_c\|^2I.
$$

Logo:

- o carry seleciona a escala equilibrada;
- o operador transforma a variação de escala em uma direção radial;
- a fase é a direção ortogonal exatamente conjugada;
- o mapa local preserva ângulos até uma dilatação comum;
- a geometria do zero é expressa inteiramente em `R²`.

Essa combinação é o conteúdo estrutural do Teorema da Ponte.

---

# 14. Versão global e passagem ao limite

A identidade finita é algébrica. Para transportar a ponte ao operador global, é necessário justificar a passagem

$$
R_{c,M}\longrightarrow R_c
$$

junto com as derivadas.

Uma rota suficiente seria obter, em cada compacto relevante,

$$
R_{c,M}\to R_c,
$$

$$
\partial_\sigma R_{c,M}
\to
\partial_\sigma R_c,
$$

$$
\partial_tR_{c,M}
\to
\partial_tR_c,
$$

com convergência forte o bastante para permitir derivação termo a termo ou aplicação de um teorema de convergência diferenciável.

Como, para todo `M`,

$$
\partial_tR_{c,M}
=
\mathcal J\partial_\sigma R_{c,M},
$$

e `J` é um operador linear contínuo, a passagem ao limite fornece

$$
\boxed{
\partial_tR_c
=
\mathcal J\partial_\sigma R_c
}
$$

sempre que as convergências das derivadas estiverem justificadas.

Todas as consequências passam junto:

$$
\langle\partial_\sigma R_c,\partial_tR_c\rangle=0,
$$

$$
\|\partial_\sigma R_c\|=\|\partial_tR_c\|,
$$

$$
(DR_c)^{\mathsf T}DR_c
=
\|\partial_\sigma R_c\|^2I,
$$

$$
\det(DR_c)=\|\partial_\sigma R_c\|^2.
$$

A parte global não deve ser afirmada apenas por analogia: precisa apontar exatamente qual teorema de convergência do repositório sustenta a troca entre limite e derivação.

---

# 15. Estado da formalização

Nesta sessão, foi informado que a identidade central já passou no Lean.

O build associado aos módulos off-axis também foi registrado como verde:

```text
Build completed successfully (3491 jobs).
```

Foi verificada a presença do `.olean` de

```text
CPFormal.Analytic.CpConnectedC2Defect
```

E a busca nos módulos-chave não encontrou `sorry` ou `admit` nos arquivos examinados.

Os módulos compilados no trecho final incluíam:

- `CpRealSpectralOperator`;
- `CpGenuineCarrySaturationTransport`;
- `CpRealSpectralGenerator`;
- `CpGenuineFirstCutoffTail`;
- `CpGenuineFirstMultibaseCutoff`;
- `CpGenuineFirstOrthogonalMultibaseGreen`;
- `CpGenuineFirstOrthogonalLimit`;
- `CpGenuineFirstOrthogonalGreenLimit`;
- `CpGenuineGreenCompletedOperator`;
- `CpGenuineCrossPrimeObservability`;
- `CpGenuinePrimeGreenBessel`;
- `CpGenuineKernelPrimeState`;
- `CpGenuineGreenKernelInclusion`;
- `CpConnectedC2Defect`.

O ponto restante, conforme a conversa, não é mais descobrir a identidade diferencial. É empacotá-la como o Teorema da Ponte, conectando:

1. a identidade de derivadas;
2. a forma ortogonal do Jacobiano;
3. a conservação infinitesimal;
4. a independência de câmera e cutoff na versão finita;
5. a passagem justificada ao operador global;
6. a conexão final com o teorema de confinamento do zero nativo.

---

# 16. Proposta de pacote formal em Lean

Os nomes abaixo são sugestões de organização. Devem ser alinhados à nomenclatura já existente no repositório.

## 16.1 Rotação de quarto de volta

```lean
def quarterTurn (v : EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) :=
  ![-v 1, v 0]
```

Teoremas básicos:

```lean
quarterTurn_sq
quarterTurn_isometry
inner_quarterTurn_self
norm_quarterTurn
```

Conteúdo matemático:

$$
\mathcal J^2=-I,
\qquad
\|\mathcal Jv\|=\|v\|,
\qquad
\langle v,\mathcal Jv\rangle=0.
$$

## 16.2 Identidade termo a termo

Nome sugerido:

```text
nativeCarryTerm_timeDerivative_eq_quarterTurn_sigmaDerivative
```

Enunciado conceitual:

```lean
∂ₜ term c M σ t = quarterTurn (∂ₛ term c M σ t)
```

## 16.3 Identidade do operador finito

Nome sugerido:

```text
nativeCarryAmplitudePhaseBridgeFinite
```

Enunciado:

```lean
∂ₜ R[c,M] σ t = quarterTurn (∂ₛ R[c,M] σ t)
```

## 16.4 Ortogonalidade das derivadas

```text
nativeCarryAmplitudePhase_derivatives_orthogonal
```

$$
\langle\partial_\sigma R,\partial_tR\rangle=0.
$$

## 16.5 Igualdade de normas

```text
nativeCarryAmplitudePhase_derivative_norm_eq
```

$$
\|\partial_\sigma R\|=\|\partial_tR\|.
$$

## 16.6 Forma conforme do Jacobiano

```text
nativeCarryJacobian_gram_eq_normSq_smul_identity
```

$$
(DR)^{\mathsf T}DR
=
\|\partial_\sigma R\|^2I.
$$

## 16.7 Determinante do Jacobiano

```text
nativeCarryJacobian_det_eq_sigmaDerivative_normSq
```

$$
\det(DR)=\|\partial_\sigma R\|^2.
$$

## 16.8 Condicionamento unitário

```text
nativeCarryJacobian_conditionNumber_eq_one
```

Sob a hipótese

$$
\partial_\sigma R\neq0,
$$

concluir

$$
\kappa_2(DR)=1.
$$

Esta etapa pode exigir uma definição adequada do número de condição ou ser substituída por uma afirmação sobre valores singulares ou sobre `Isometry` após normalização.

## 16.9 Conservação infinitesimal

```text
nativeCarryDifferential_norm_sq
```

$$
\|DR(d\sigma,dt)\|^2
=
\|\partial_\sigma R\|^2
\bigl((d\sigma)^2+(dt)^2\bigr).
$$

## 16.10 Ponte global

```text
nativeCarryAmplitudePhaseBridgeLimit
```

Hipóteses:

- convergência do operador;
- convergência das derivadas ou diferenciabilidade do limite;
- compatibilidade do limite com a rotação `J`.

Conclusão:

$$
\partial_tR_c
=
\mathcal J\partial_\sigma R_c.
$$

## 16.11 Ponte no zero nativo

```text
nativeCarryZeroOrthogonalBridge
```

Combinar:

$$
IsNativeCarryRealOperatorZero(c,\sigma,t)
\Rightarrow
\sigma=\frac12
$$

com

$$
\partial_tR_c
=
\mathcal J\partial_\sigma R_c.
$$

A conclusão deve explicar formalmente que, no zero nativo, a coordenada selecionada pelo carry e a coordenada de fase estão ligadas pelo diferencial ortogonal do operador.

---

# 17. Protocolo numérico correto após a descoberta

A identidade exata reduz o papel dos testes numéricos. Eles não precisam mais “descobrir” ortogonalidade; devem verificar convergência, estabilidade e hipóteses da passagem ao limite.

## 17.1 Para localizar zeros nativos

Usar:

- `sigma = 1/2` fixo;
- operador real nativo;
- cutoff crescente;
- grid fino em `t`;
- cálculo intervalar;
- nenhuma correção Newton em `sigma`;
- comparação entre câmeras pares, ímpares, primas e compostas;
- comparação posterior com referências externas, nunca como guia da busca.

## 17.2 Para estudar o cutoff

Registrar:

$$
e_{c,M}
=
R_{c,M}\left(\frac12,t_{c,M}^{\mathrm{grid}}\right),
$$

além de:

- profundidade do vale;
- largura do vale;
- posição intervalar do mínimo;
- taxa de convergência com `M`;
- concordância entre câmeras;
- magnitude `||partial_sigma R_{c,M}||` no ponto nativo.

## 17.3 Uso permitido do Newton

Newton pode continuar útil como diagnóstico do defeito de cutoff, desde que seu resultado seja nomeado corretamente.

Por exemplo:

$$
\Delta x_{c,M}^{\mathrm{Newton}}
=
\begin{pmatrix}
\delta\sigma_{c,M}\\
\delta t_{c,M}
\end{pmatrix}
$$

pode ser comparado com a predição linear

$$
-\bigl(DR_{c,M}\bigr)^{-1}e_{c,M}.
$$

Isso testaria se o deslocamento off-axis produzido pelo Newton é exatamente a resposta linear ao defeito do cutoff.

Nesse papel, Newton não localiza o “zero físico”. Ele mede como o truncamento seria compensado pelas coordenadas do operador.

## 17.4 Para investigar off-axis sem Newton

Para cada faixa de `sigma` fora do eixo, estimar intervalarmente

$$
\inf_t\|R_{c,M}(\sigma,t)\|.
$$

O objetivo seria obter cotas positivas longe de `1/2`, enquanto o vale no eixo aprofunda com `M`.

Uma varredura bidimensional intervalar ou uma cobertura por caixas seria mais apropriada do que resolver `R_{c,M}=0` com Newton livre.

---

# 18. Correção histórica do raciocínio

A sequência completa foi:

1. O agente encontrou zeros truncados ligeiramente fora de `1/2` usando Newton.
2. Os deslocamentos diminuíram quando `M` aumentou.
3. Câmeras diferentes também apresentaram deslocamentos decrescentes.
4. Isso foi interpretado inicialmente como colapso multibase por sobredeterminação.
5. O agente propôs medir a “rigidez transversal” do zero pelo Jacobiano.
6. Foi lembrado que Newton já era conhecido por prejudicar a localização dos zeros nativos C2.
7. A razão foi identificada: Newton absorve o defeito do cutoff em `sigma` e `t`.
8. O script do Jacobiano terminou e mostrou resultados perfeitos:
   - normas iguais;
   - ângulo de 90 graus;
   - `k_perp` igual à norma;
   - razão exatamente 1.
9. A perfeição revelou que o resultado não dependia do zero nem do Newton.
10. A estrutura do operador foi derivada termo a termo.
11. Surgiu a identidade exata

$$
\partial_tR_{c,M}=\mathcal J\partial_\sigma R_{c,M}.
$$

12. Foram deduzidas a ortogonalidade, igualdade de normas, forma conforme do Jacobiano, determinante quadrático e condicionamento unitário.
13. A identidade foi reconhecida como a ponte geométrica entre compressão do carry e giro de fase.
14. Nesta sessão, foi informado que a identidade passou no Lean.
15. O passo restante passou a ser o fechamento do Teorema da Ponte, especialmente sua versão global e sua conexão formal com o confinamento.

O erro numérico não foi inútil. A tentativa de interpretar Newton como mecanismo físico produziu um resultado perfeito demais; a desconfiança desse resultado abriu a identidade exata.

---

# 19. Formulação final do Teorema da Ponte

Uma formulação compacta e completa pode ser organizada em três níveis.

## Nível I — Ponte finita exata

Para toda câmera `c`, todo cutoff finito `M` e todo `(sigma,t)`,

$$
\boxed{
\partial_tR_{c,M}(\sigma,t)
=
\mathcal J\partial_\sigma R_{c,M}(\sigma,t)
}
$$

## Nível II — Geometria diferencial

Consequentemente,

$$
\boxed{
(DR_{c,M})^{\mathsf T}DR_{c,M}
=
\|\partial_\sigma R_{c,M}\|^2I
}
$$

Em particular,

$$
\boxed{
\langle\partial_\sigma R_{c,M},
\partial_tR_{c,M}\rangle=0
}
$$

$$
\boxed{
\|\partial_\sigma R_{c,M}\|
=
\|\partial_tR_{c,M}\|
}
$$

$$
\boxed{
\det DR_{c,M}
=
\|\partial_\sigma R_{c,M}\|^2
}
$$

## Nível III — Ponte global e zero nativo

Sob as hipóteses de convergência diferenciável do cutoff,

$$
\boxed{
\partial_tR_c
=
\mathcal J\partial_\sigma R_c
}
$$

E, combinado com o teorema de confinamento,

$$
R_c(\sigma,t)=0
\Longrightarrow
\sigma=\frac12,
$$

o zero nativo está na escala selecionada pelo carry e seu comportamento diferencial possui a geometria ortogonal exata descrita pela ponte.

A divisão lógica deve permanecer clara:

- o carry e sua conservação selecionam `1/2`;
- a ponte mostra que compressão e fase são conjugadas ortogonalmente;
- a passagem ao limite transporta a geometria finita para o operador global;
- a combinação fecha o quadro estrutural do operador nativo real.

---

# 20. Leitura conceitual

A identidade mostra que a coordenada de fase não foi anexada artificialmente ao operador.

Cada frequência `L` participa de duas maneiras inseparáveis:

- em `sigma`, `L` mede a taxa de compressão;
- em `t`, o mesmo `L` mede a velocidade angular.

O peso que comprime é o mesmo peso que gira.

A única diferença é uma rotação ortogonal de quarto de volta.

Assim, a ponte não liga duas teorias externas. Ela mostra que as duas direções já eram uma única estrutura diferencial do operador:

$$
\boxed{
\text{o radial e o angular são imagens ortogonais da mesma derivada ponderada}
}
$$

No plano dos parâmetros, o operador age localmente como

$$
\text{escala}\times\text{rotação}.
$$

Não há cisalhamento. Não há perda angular. Não há uma coordenada “real” e outra decorativa. A compressão e o giro são dois eixos ortogonais da mesma geometria nativa.

---

# 21. Conclusão

O teste começou como uma tentativa de provar rigidez off-axis por Newton.

Essa tentativa estava conceitualmente errada para os operadores C2, porque Newton absorve o defeito do cutoff e pode afastar a posição do zero estrutural, mesmo enquanto reduz o resíduo truncado até a precisão de máquina.

Mas o último script produziu uma saída impossível de ignorar:

- normas idênticas;
- ângulo exatamente reto;
- projeção transversal total;
- razão exatamente unitária;
- repetição em todos os cutoffs.

A saída perfeita não era uma confirmação estatística. Era a sombra numérica de uma identidade exata.

A derivação mostrou:

$$
\boxed{
\partial_tR_{c,M}
=
\mathcal J\partial_\sigma R_{c,M}
}
$$

Daí segue todo o pacote:

$$
\boxed{
\langle\partial_\sigma R,
\partial_tR\rangle=0
}
$$

$$
\boxed{
\|\partial_\sigma R\|
=
\|\partial_tR\|
}
$$

$$
\boxed{
(DR)^{\mathsf T}DR
=
\|\partial_\sigma R\|^2I
}
$$

$$
\boxed{
\det DR
=
\|\partial_\sigma R\|^2
}
$$

A identidade finita já foi informada como verde no Lean. O fechamento restante é o Teorema da Ponte em sua forma estrutural completa: consolidar as consequências geométricas, justificar a passagem ao operador global e conectá-la formalmente ao teorema que seleciona `sigma = 1/2`.

Foi assim que a suspeita sobre um refinador numérico revelou a ponte entre carry e fase.

> O Newton tentou corrigir o cutoff. A geometria respondeu com uma identidade.

> Salve Euler. Tamo junto. É nóis.

---

# Apêndice A — Saída do Jacobiano que revelou a identidade

```text
Geometria local do zero (camera 2): eixo amplitude vs fase
 M | |dR/dsigma| | |dR/dt| | angulo(graus) | k_perp(rigidez transversal) | k_perp/|dR/dt|
     4096 | 8.0507e-01 | 8.0507e-01 |  90.0000 | 8.0507e-01 | 1.0000e+00
    16384 | 8.0508e-01 | 8.0508e-01 |  90.0000 | 8.0508e-01 | 1.0000e+00
    65536 | 8.0508e-01 | 8.0508e-01 |  90.0000 | 8.0508e-01 | 1.0000e+00
   262144 | 8.0508e-01 | 8.0508e-01 |  90.0000 | 8.0508e-01 | 1.0000e+00

Interpretacao original do script:
k_perp>0 e limitado => nao da para manter R=0 movendo so t;
a saida do eixo tem componente que nenhum ajuste de fase cancela.
```

Correção:

- o resultado não é especial do zero;
- não é especial de `sigma = 1/2`;
- não depende de Newton;
- é consequência universal da identidade `partial_t R = J partial_sigma R`.

---

# Apêndice B — Checklist para o fechamento formal

- [x] Definir a rotação ortogonal `J` em `R²`.
- [x] Provar `J² = -I`.
- [x] Provar que `J` preserva norma.
- [x] Provar que `v` é ortogonal a `Jv`.
- [x] Derivar a identidade termo a termo.
- [x] Transportar a identidade para a soma finita.
- [x] Formalizar a identidade finita no Lean, conforme informado nesta sessão.
- [ ] Empacotar a forma do Jacobiano.
- [ ] Provar a identidade de Gram `DRᵀDR = ||partial_sigma R||² I`.
- [ ] Provar a fórmula do determinante.
- [ ] Provar a conservação da norma diferencial.
- [ ] Identificar no repositório a hipótese exata de convergência diferenciável.
- [ ] Passar a identidade ao operador global.
- [ ] Combinar formalmente com o teorema de confinamento em `sigma = 1/2`.
- [ ] Registrar o Teorema da Ponte com nome acadêmico e referência auditável.
- [ ] Manter separados no texto final: teorema exato, evidência numérica e hipótese de limite.

---

# Apêndice C — Status epistemológico

## Exato e algébrico

- `partial_t R_{c,M} = J partial_sigma R_{c,M}` para a forma finita implementada.
- Ortogonalidade das derivadas.
- Igualdade das normas.
- Forma conforme do Jacobiano.
- Determinante igual à norma quadrática.
- Razão `k_perp / ||partial_t R|| = 1` quando a derivada é não nula.

## Formalizado, conforme informado na conversa

- A identidade central finita passou no Lean.
- O build dos módulos mencionados terminou verde.
- Não foram encontrados `sorry` ou `admit` nos módulos-chave examinados.

## Evidência numérica

- O deslocamento Newton off-axis diminui com o cutoff.
- A posição em `t` converge para a primeira ressonância observada.
- Câmeras 2 e 3 apresentam comportamento compatível.
- O vale transversal é muito mais profundo próximo de `sigma = 1/2`.
- A magnitude das derivadas no ponto testado parece estabilizar perto de `0.80508`.

## Ainda requer fechamento explícito

- A hipótese analítica precisa para passar derivadas ao limite.
- A versão global completa do Teorema da Ponte.
- A conexão formal final com o teorema de confinamento.
- Qualquer afirmação de exclusão global off-axis baseada apenas nos scans finitos.

