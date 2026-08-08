# Auditoria de completude das câmeras e colapso do bulk

## Resultado principal

O experimento separa duas noções que estavam misturadas:

- **bulk vertical:** linhas TFVD em profundidade b-ádica `k >= 2`;
- **interior horizontal nativo:** brackets completos `f(c-r)-2f(c)+f(c+r)`.

A remoção de câmeras horizontalmente incompletas reduz o colapso do modelo vertical, mas não o elimina. Em contraste, o setor de brackets horizontais completos permanece dominante na média quadrática do frame. Logo, o no-go vertical não pode ser interpretado como desaparecimento da curvatura nativa.

## Cortes testados

- `all`: todas as bases `2 <= b <= N`;
- `complete_exact`: a primeira célula nativa completa cabe no cutoff;
- `two_b`: regra conservadora `2b <= N`;
- `vertical_mature`: `b <= sqrt(N)`, para comparar com a condição de profundidade vertical.

No scanner nativo atual, a primeira célula natural completa exige `b + floor(b/2) <= N`; para C2, o primeiro bracket completo usa `3,4,5`. A regra `2b <= N` é mais restritiva, mas segura.

## 1. Modelo vertical antigo — norma quadrática do bulk

| N | todas b≤N | célula completa | 2b≤N | b≤√N |
|---:|---:|---:|---:|---:|
| 16 | 0.098414 | 0.183499 | 0.293790 | 0.707391 |
| 32 | 0.028904 | 0.062703 | 0.100944 | 0.606661 |
| 64 | 0.010343 | 0.022361 | 0.039197 | 0.438389 |
| 128 | 0.003154 | 0.007091 | 0.012384 | 0.309654 |
| 256 | 0.001083 | 0.002420 | 0.004305 | 0.238641 |

A filtragem por completude horizontal atrasa a diluição, mas o bulk vertical ainda cai porque uma linha vertical de bulk exige três níveis `m,bm,b²m`; isso é uma condição diferente de possuir esquerda–centro–direita na câmera nativa.

## 2. Geometria horizontal nativa — fração média de bracket no frame

| N | todas b≤N | célula completa | 2b≤N |
|---:|---:|---:|---:|
| 16 | 0.713554 | 0.774366 | 0.799034 |
| 32 | 0.765139 | 0.829101 | 0.857140 |
| 64 | 0.793180 | 0.852253 | 0.882974 |
| 128 | 0.806897 | 0.867006 | 0.896126 |
| 256 | 0.816710 | 0.875225 | 0.904558 |

A fração quadrática média dos brackets completos não colapsou. Ela cresce quando bases sem uma célula completa são retiradas.

## 3. Energia do estado nativo em t = 14.134725141734695

| N | todas b≤N | célula completa | 2b≤N |
|---:|---:|---:|---:|
| 16 | 0.601459 | 0.723729 | 0.765948 |
| 32 | 0.552659 | 0.688669 | 0.728886 |
| 64 | 0.504553 | 0.632163 | 0.676261 |
| 128 | 0.456874 | 0.585591 | 0.627336 |
| 256 | 0.417248 | 0.540386 | 0.581342 |

Essa fração é dependente do estado e do tempo. Ela permanece majoritária nos cortes completos até N=256, mas a tabela não constitui prova de limite positivo.

## 4. Controle: medida pitagórica derivada do carry

| N | endpoint mínimo | bulk normalizado² | norma Poisson |
|---:|---:|---:|---:|
| 16 | 0.407314 | 0.592686 | 1.206278 |
| 32 | 0.414754 | 0.585246 | 1.187884 |
| 64 | 0.421400 | 0.578600 | 1.171769 |
| 128 | 0.425732 | 0.574268 | 1.161419 |
| 256 | 0.428057 | 0.571943 | 1.155913 |

Com a divisão pitagórica `mu_G=omega/b` e `mu_R=omega(1-1/b)`, o bulk vertical permanece não trivial no intervalo testado.

## Conclusão

1. A fronteira de câmeras incompletas é um artefato real do corte `b <= N`.
2. O colapso provado pelo script antigo pertence ao bulk vertical b-ádico, não ao bracket horizontal nativo.
3. O bracket horizontal completo não desapareceu nas métricas testadas.
4. Para preservar também o bulk vertical no atlas infinito, a medida pitagórica do carry é o controle que passou.

Portanto, a interpretação correta é: **completude da câmera resolve a leitura horizontal; ponderação derivada do carry resolve a competição vertical entre quantidade de bases e profundidade.**

## Reprodutibilidade

- Script: `native_carry_camera_completeness_audit.py`
- Dados: `camera_completeness_audit.json`
