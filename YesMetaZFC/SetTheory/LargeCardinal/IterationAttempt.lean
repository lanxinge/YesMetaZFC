import YesMetaZFC.SetTheory.LargeCardinal.IterationDiagram
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingAttemptDecode
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingAttemptSyntax
import YesMetaZFC.Model.SetTheory.Internal.SourceClosureSyntax
import YesMetaZFC.SetTheory.Notation

/-! # 整条有限树枝的联合初等尝试

节点为 (k,P)：P 为 k 的全部树前驱各存一行，行长恰为 k。
各行检验全部内部公式，并在原树嵌入下交换；根行遵守指定嵌入。
末结点递增时只延长原来的行，所以内部无限链同时给出共尾枝和相容实现。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

structure Ja_enum_d (ω α Q E : M.Domain) : Prop where
  function : M.IsSetFunction I E
  domain : M.IsDomainOf I α E
  rows : ∀ i e c X R, Rd_entry_d i e E → Rd_entry_d i c Q → KPair_d M c X R →
    Fn0_d ω X e ∧ ∀ x, M.mem x X → ∃ n, M.mem n ω ∧ Rd_entry_d n x e

def Ja_rows_d (ω Q E Y W k P : M.Domain) : Prop := ∀ i p c X R e,
  Rd_entry_d i p P → Rd_entry_d i c Q → KPair_d M c X R → Rd_entry_d i e E →
    Fn0_d k Y p ∧ At_coherent_d k X Y e p ∧ At_elementary_d I ω X R Y W e k p

def Ja_commute_d (G E P : M.Domain) : Prop := ∀ i j p q e f g u v x y a b,
  Rd_entry_d i p P → Rd_entry_d j q P → Rd_entry_d i e E → Rd_entry_d j f E →
    It_map_d G i j g → Rd_entry_d u x e → Rd_entry_d v y f → Rd_entry_d x y g →
      Rd_entry_d u a p → Rd_entry_d v b q → a = b

structure Ja_node_d (ω T Q G E Y W z π k P : M.Domain) : Prop where
  length : M.mem k ω
  function : M.IsSetFunction I P
  domain : ∀ i, (∃ p, Rd_entry_d i p P) ↔ Rd_entry_d i k T
  rows : Ja_rows_d I ω Q E Y W k P
  root : ∀ p c X R e, Rd_entry_d z p P → Rd_entry_d z c Q → KPair_d M c X R → Rd_entry_d z e E →
    At_prescribed_d k X Y e π p
  commute : Ja_commute_d G E P

def Ja_extend_d (T s t : M.Domain) : Prop := ∃ k P l Q,
  KPair_d M s k P ∧ KPair_d M t l Q ∧ M.mem k l ∧ Rd_entry_d k l T ∧
    ∀ i p q, Rd_entry_d i p P → Rd_entry_d i q Q → M.MemberSubset p q

/-- 此处直接编码全部有限赋值检验；不缩减为原子真值或外部公式。 -/
def ja_elementary_m {d} (ω X R Y W e k p : Term d) : Formula 1 d := set[d] ⟪
  ∀ b l F A B q s t, b ∈ ⌜ω⌝ₛ → ⌜sfm_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, l, F) →
    ⌜sbound_m (𝒞 := kpair_convention_l)⌝ₚ(F, b) →
    ⌜Formula.isFunctionSpace kpair_convention_l⌝ₚ(A, b, ⌜X⌝ₛ) →
    ⌜Formula.isFunctionSpace kpair_convention_l⌝ₚ(B, b, ⌜Y⌝ₛ) → ⌜fn0_m⌝ₚ(b, ⌜k⌝ₛ, q) →
    ⌜cp0_m⌝ₚ(b, ⌜ω⌝ₛ, ⌜X⌝ₛ, q, ⌜e⌝ₛ, s) → ⌜cp0_m⌝ₚ(b, ⌜k⌝ₛ, ⌜Y⌝ₛ, q, ⌜p⌝ₛ, t) →
    ∀ r ∈ l, ⌜ssat_m (𝒞 := kpair_convention_l)⌝ₚ(⌜X⌝ₛ, ⌜R⌝ₛ, A, F, l, r, s) ↔
      ⌜ssat_m (𝒞 := kpair_convention_l)⌝ₚ(⌜Y⌝ₛ, ⌜W⌝ₛ, B, F, l, r, t)⟫
derive_free_closed ja_elementary_m

theorem ja_elementary_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω X R Y W e k p : Term d) :
    Formula.satisfies ρ (ja_elementary_m ω X R Y W e k p) ↔
      At_elementary_d I (ω.eval ρ) (X.eval ρ) (R.eval ρ) (Y.eval ρ) (W.eval ρ) (e.eval ρ) (k.eval ρ) (p.eval ρ) := by
  simp only [ja_elementary_m, At_elementary_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, sfm_sat_l I hE, sbound_sat_l I, Formula.satisfies_isFunctionSpace_iff I hE,
    fn0_sat_l hE, cp0_sat_l hE, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    ssat_sat_l I hE, Definitional.Term.eval_weaken]; rfl

def ja_rows_m {d} (ω Q E Y W k P : Term d) : Formula 1 d := set[d] ⟪
  ∀ i p c X R e, ⌜rd_entry0_m⌝ₚ(i, p, ⌜P⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) →
    ⌜kpair_m⌝ₚ(c, X, R) → ⌜rd_entry0_m⌝ₚ(i, e, ⌜E⌝ₛ) →
    ⌜fn0_m⌝ₚ(⌜k⌝ₛ, ⌜Y⌝ₛ, p) ∧ ⌜at_coherent_m⌝ₚ(⌜k⌝ₛ, X, ⌜Y⌝ₛ, e, p) ∧
      ⌜ja_elementary_m⌝ₚ(⌜ω⌝ₛ, X, R, ⌜Y⌝ₛ, ⌜W⌝ₛ, e, ⌜k⌝ₛ, p)⟫
derive_free_closed ja_rows_m

theorem ja_rows_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω Q E Y W k P : Term d) :
    Formula.satisfies ρ (ja_rows_m ω Q E Y W k P) ↔
      Ja_rows_d I (ω.eval ρ) (Q.eval ρ) (E.eval ρ) (Y.eval ρ) (W.eval ρ) (k.eval ρ) (P.eval ρ) := by
  simp only [ja_rows_m, Ja_rows_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hE, kpair_sat_l M hE, Formula.satisfies_conj_iff, fn0_sat_l hE,
    at_coherent_sat_l hE, ja_elementary_sat_l I hE, Definitional.Term.eval_weaken]; rfl

def ja_commute_m {d} (G E P : Term d) : Formula 1 d := set[d] ⟪
  ∀ i j p q e f g u v x y a b,
    ⌜rd_entry0_m⌝ₚ(i, p, ⌜P⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j, q, ⌜P⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(i, e, ⌜E⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j, f, ⌜E⌝ₛ) → ⌜it_map_m⌝ₚ(⌜G⌝ₛ, i, j, g) →
    ⌜rd_entry0_m⌝ₚ(u, x, e) → ⌜rd_entry0_m⌝ₚ(v, y, f) → ⌜rd_entry0_m⌝ₚ(x, y, g) →
    ⌜rd_entry0_m⌝ₚ(u, a, p) → ⌜rd_entry0_m⌝ₚ(v, b, q) → a = b⟫
derive_free_closed ja_commute_m

theorem ja_commute_sat_l (hE : Extensional M) {d} (ρ : Env M d) (G E P : Term d) :
    Formula.satisfies ρ (ja_commute_m G E P) ↔ Ja_commute_d (G.eval ρ) (E.eval ρ) (P.eval ρ) := by
  simp only [ja_commute_m, Ja_commute_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hE, it_map_sat_l hE, Formula.satisfies_extensionalEq_iff_eq hE,
    Definitional.Term.eval_weaken]; rfl

def ja_node_m {d} (ω T Q G E Y W z π k P : Term d) : Formula 1 d := set[d] ⟪
  ⌜k⌝ₛ ∈ ⌜ω⌝ₛ ∧ ⌜Formula.isFunction kpair_convention_l⌝ₚ(⌜P⌝ₛ) ∧
    (∀ i, (∃ p, ⌜rd_entry0_m⌝ₚ(i, p, ⌜P⌝ₛ)) ↔ ⌜rd_entry0_m⌝ₚ(i, ⌜k⌝ₛ, ⌜T⌝ₛ)) ∧
    ⌜ja_rows_m⌝ₚ(⌜ω⌝ₛ, ⌜Q⌝ₛ, ⌜E⌝ₛ, ⌜Y⌝ₛ, ⌜W⌝ₛ, ⌜k⌝ₛ, ⌜P⌝ₛ) ∧
    (∀ p c X R e, ⌜rd_entry0_m⌝ₚ(⌜z⌝ₛ, p, ⌜P⌝ₛ) → ⌜rd_entry0_m⌝ₚ(⌜z⌝ₛ, c, ⌜Q⌝ₛ) →
      ⌜kpair_m⌝ₚ(c, X, R) → ⌜rd_entry0_m⌝ₚ(⌜z⌝ₛ, e, ⌜E⌝ₛ) →
        ⌜at_prescribed_m⌝ₚ(⌜k⌝ₛ, X, ⌜Y⌝ₛ, e, ⌜π⌝ₛ, p)) ∧ ⌜ja_commute_m⌝ₚ(⌜G⌝ₛ, ⌜E⌝ₛ, ⌜P⌝ₛ)⟫
derive_free_closed ja_node_m

theorem ja_node_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω T Q G E Y W z π k P : Term d) :
    Formula.satisfies ρ (ja_node_m ω T Q G E Y W z π k P) ↔
      Ja_node_d I (ω.eval ρ) (T.eval ρ) (Q.eval ρ) (G.eval ρ) (E.eval ρ) (Y.eval ρ) (W.eval ρ)
        (z.eval ρ) (π.eval ρ) (k.eval ρ) (P.eval ρ) := by
  simp only [ja_node_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isFunction_iff I hE, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_exists_iff, rd_entry0_sat_l hE, ja_rows_sat_l I hE, Formula.satisfies_imp_iff,
    kpair_sat_l M hE, at_prescribed_sat_l hE, ja_commute_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩,
    fun h => ⟨h.length, h.function, h.domain, h.rows, h.root, h.commute⟩⟩

def ja_extend_m {d} (T s t : Term d) : Formula 1 d := set[d] ⟪
  ∃ k P l Q, ⌜kpair_m⌝ₚ(⌜s⌝ₛ, k, P) ∧ ⌜kpair_m⌝ₚ(⌜t⌝ₛ, l, Q) ∧ k ∈ l ∧
    ⌜rd_entry0_m⌝ₚ(k, l, ⌜T⌝ₛ) ∧ (∀ i p q, ⌜rd_entry0_m⌝ₚ(i, p, P) → ⌜rd_entry0_m⌝ₚ(i, q, Q) → p ⊆ q)⟫
derive_free_closed ja_extend_m

theorem ja_extend_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T s t : Term d) :
    Formula.satisfies ρ (ja_extend_m T s t) ↔ Ja_extend_d (T.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [ja_extend_m, Ja_extend_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, Formula.satisfies_mem_iff, rd_entry0_sat_l hE, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.LargeCardinal
