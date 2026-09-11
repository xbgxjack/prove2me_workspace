import Mathlib

set_option autoImplicit false

open Metric Matrix

namespace ReservoirESN

/-- **Equation de reservoir, indexee par le passe.** L'article ecrit
`x_t = F(x_{t-1}, z_t)` pour `t ∈ ℤ_-`. En posant `X k := x_{-k}` et `Z k := z_{-k}`,
cela devient `X k = F (X (k+1)) (Z k)` : l'indice `k` compte les pas dans le passe,
`k = 0` etant le present. -/
def IsSolution {E S : Type*} [NormedAddCommGroup E] [NormedAddCommGroup S]
    (F : S → E → S) (z : ℕ → E) (x : ℕ → S) : Prop :=
  ∀ k, x k = F (x (k + 1)) (z k)

/-- Suites uniformement bornees par `M` : le `K_M` de l'article, eq. (2.14). -/
def UnifBdd {E : Type*} [NormedAddCommGroup E] (M : ℝ) (z : ℕ → E) : Prop :=
  ∀ k, ‖z k‖ ≤ M

/-- Une application de reservoir est **contractante** de rapport `r` sur les boules
`B(0,L) × B(0,M)` lorsqu'elle y laisse `B(0,L)` invariante et contracte l'etat
uniformement en l'entree. Les rayons sont strictement positifs, comme dans la
source (« Let M > 0 »), ce qui empeche que les hypotheses soient vides. -/
structure IsContracting {E S : Type*} [NormedAddCommGroup E] [NormedAddCommGroup S]
    (F : S → E → S) (L M r : ℝ) : Prop where
  nonneg : 0 ≤ r
  lt_one : r < 1
  state_radius_pos : 0 < L
  input_radius_pos : 0 < M
  maps_to : ∀ x w, ‖x‖ ≤ L → ‖w‖ ≤ M → ‖F x w‖ ≤ L
  contract : ∀ x y w, ‖x‖ ≤ L → ‖y‖ ≤ L → ‖w‖ ≤ M → ‖F x w - F y w‖ ≤ r * ‖x - y‖

/-- Une **suite de ponderation** au sens de la Definition 2.5 : `w : ℕ → (0,1]`,
decroissante et tendant vers zero. `w k` pondere l'instant situe `k` pas dans le passe. -/
structure IsWeighting (w : ℕ → ℝ) : Prop where
  pos : ∀ k, 0 < w k
  le_one : ∀ k, w k ≤ 1
  antitone : Antitone w
  tendsto_zero : Filter.Tendsto w Filter.atTop (nhds 0)

/-- Norme ponderee `‖z‖_w = sup_k ‖z k‖ * w k` de la Definition 2.5, sous la forme
« majorant » : `WeightedBound w z c` dit que `c` majore cette borne superieure. -/
def WeightedBound {E : Type*} [NormedAddCommGroup E] (w : ℕ → ℝ) (z : ℕ → E) (c : ℝ) : Prop :=
  ∀ k, ‖z k‖ * w k ≤ c

/-- **Propriete de memoire evanescente** (Definition 2.5) pour l'application
entree ↦ etat present, exprimee en `ε`-`δ` avec la norme ponderee. -/
def HasFadingMemory {E S : Type*} [NormedAddCommGroup E] [NormedAddCommGroup S]
    (F : S → E → S) (L M : ℝ) (w : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ z z' : ℕ → E, ∀ x x' : ℕ → S,
    UnifBdd M z → UnifBdd M z' → UnifBdd L x → UnifBdd L x' →
    IsSolution F z x → IsSolution F z' x' →
    WeightedBound w (fun k => z k - z' k) δ →
    ‖x 0 - x' 0‖ < ε

/-- **Continuite uniforme en l'entree** sur les boules `B(0,L) × B(0,M)`.
La source suppose l'application de reservoir continue (Theoreme 3.1) et travaille en
dimension finie, ou la continuite sur un compact est automatiquement uniforme. En
dimension quelconque cette uniformite doit etre demandee : sans elle deux entrees
arbitrairement proches peuvent produire des etats eloignes, et la memoire evanescente
est en defaut. -/
def UnifContInput {E S : Type*} [NormedAddCommGroup E] [NormedAddCommGroup S]
    (F : S → E → S) (L M : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : S, ∀ z z' : E,
    ‖x‖ ≤ L → ‖z‖ ≤ M → ‖z'‖ ≤ M → ‖z - z'‖ < δ → ‖F x z - F x z'‖ < ε

/-- **Memoire evanescente d'une fonctionnelle.** Une fonctionnelle envoie une suite
d'entrees sur la valeur presente de la sortie. Par la Proposition 2.12 de la source,
filtres causaux invariants et fonctionnelles se correspondent bijectivement, la FMP
d'un cote equivalant a celle de l'autre ; travailler avec la fonctionnelle est donc
fidele et evite d'avoir a formaliser separement causalite et invariance temporelle. -/
def FunctionalFMP {E S : Type*} [NormedAddCommGroup E] [NormedAddCommGroup S]
    (H : (ℕ → E) → S) (M : ℝ) (w : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ z z' : ℕ → E,
    UnifBdd M z → UnifBdd M z' → WeightedBound w (fun k => z k - z' k) δ →
    ‖H z - H z'‖ < ε

/-- **Equation d'un reseau a etats d'echo** : `x_k = σ(A x_{k+1} + C z_k + ζ)`,
`σ` etant appliquee composante par composante. Indexation par le passe, comme partout. -/
def IsESNSolution {n N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (Cin : Matrix (Fin N) (Fin n) ℝ)
    (ζ : EuclideanSpace ℝ (Fin N)) (σ : ℝ → ℝ)
    (z : ℕ → EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin N)) : Prop :=
  ∀ k i, x k i = σ ((A *ᵥ (EuclideanSpace.equiv (Fin N) ℝ (x (k + 1)))
      + Cin *ᵥ (EuclideanSpace.equiv (Fin n) ℝ (z k))) i + ζ i)

/-- **Fonction d'ecrasement** au sens de la source : croissante, de limites `-1` et `1`,
a valeurs dans `[-1,1]`, de limites `-1` en `-∞` et `1` en `+∞`, et lipschitzienne de
rapport `Lσ`. Les deux limites sont dans la definition de la source ; sans elles une
fonction constante passerait pour une fonction d'ecrasement. -/
structure IsSquashing (σ : ℝ → ℝ) (Lσ : ℝ) : Prop where
  lipschitz_nonneg : 0 ≤ Lσ
  range_mem : ∀ t : ℝ, σ t ∈ Set.Icc (-1 : ℝ) 1
  monotone : Monotone σ
  tendsto_atBot : Filter.Tendsto σ Filter.atBot (nhds (-1))
  tendsto_atTop : Filter.Tendsto σ Filter.atTop (nhds 1)
  lipschitz : ∀ s t : ℝ, |σ s - σ t| ≤ Lσ * |s - t|

end ReservoirESN
