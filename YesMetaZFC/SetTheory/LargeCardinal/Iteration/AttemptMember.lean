import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Branch
import YesMetaZFC.Model.SetTheory.Embedding.Range
import YesMetaZFC.SetTheory.Notation
import YesMetaZFC.SetTheory.Card.FiniteSequenceRecode
import YesMetaZFC.Model.SetTheory.Embedding.AttemptRelative
import YesMetaZFC.Model.SetTheory.Source.ClosureSyntax
import YesMetaZFC.SetTheory.Collapse.RelationSequence
import YesMetaZFC.SetTheory.LargeCardinal.Extender.EmbeddingCountable
import YesMetaZFC.Model.SetTheory.Reflection.TransitiveSequence
import YesMetaZFC.Model.SetTheory.Source.FinitePartial

/-! # 迭代树上的实际模型图与嵌入图

Q 按结点存结构码，G 按有序对 (i,j) 存完整初等嵌入。全部数据均是
对象模型中的集合；函数性、恒等与复合律允许沿任意树枝读取同一张图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def It_map_d (G i j f : M.Domain) : Prop := ∃ r, KPair_d M r i j ∧ Rd_entry_d r f G
def it_map_m {d} (G i j f : Term d) : Formula 1 d := .existsE
  (.conj (kpair_m .newest i.weaken j.weaken) (rd_entry_m .newest f.weaken G.weaken))
derive_free_closed it_map_m

theorem it_map_sat_l (hE : Extensional M) {d} (ρ : Env M d) (G i j f : Term d) :
    Formula.satisfies ρ (it_map_m G i j f) ↔ It_map_d (G.eval ρ) (i.eval ρ) (j.eval ρ) (f.eval ρ) := by
  simp only [it_map_m, It_map_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair_sat_l M hE, rd_entry_sat_l hE, Definitional.Term.eval_weaken]; rfl

def It_comp_d (f g h : M.Domain) : Prop := (∀ p, M.mem p h → ∃ x y, KPair_d M p x y) ∧
  ∀ x z, Rd_entry_d x z h ↔ ∃ y, Rd_entry_d x y f ∧ Rd_entry_d y z g
def it_comp_m {d} (f g h : Term d) : Formula 1 d := .conj
  (Formula.isRelation kpair_convention_l h) (Formula.isComposition kpair_convention_l h g f)
derive_free_closed it_comp_m

theorem it_comp_sat_l (hE : Extensional M) {d} (ρ : Env M d) (f g h : Term d) :
    Formula.satisfies ρ (it_comp_m f g h) ↔ It_comp_d (f.eval ρ) (g.eval ρ) (h.eval ρ) := by
  simp only [it_comp_m, It_comp_d, Formula.isComposition, Formula.satisfies_conj_iff,
    Formula.isRelation, Formula.orderedPairMem, kpair_convention_l,
    Formula.satisfies_forallMem_iff, kpair_sat_l M hE, Formula.satisfies_mem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_exists_iff, Rd_entry_d,
    Definitional.Term.eval_weaken]; rfl

theorem It_comp_d.unique_l (hE : Extensional M) {f g h k : M.Domain} (hh : It_comp_d f g h) (hk : It_comp_d f g k) : h = k := by
  have sub a b (ha : It_comp_d f g a) (hb : It_comp_d f g b) p (hp : M.mem p a) : M.mem p b := by
    obtain ⟨x, y, hxy⟩ := ha.1 p hp
    obtain ⟨q, hq, hqb⟩ := (hb.2 x y).mpr ((ha.2 x y).mp ⟨p, hxy, hp⟩)
    exact kpair_unique_l M hE hq hxy ▸ hqb
  exact hE.eq_of_same_members h k fun p => ⟨sub h k hh hk p, sub k h hk hh p⟩

structure It_diagram_d (I : kpair_convention_l.Interpretation M) (ω α T Q G : M.Domain) : Prop where
  order : It_order_d α T
  model_function : M.IsSetFunction I Q
  model_domain : M.IsDomainOf I α Q
  models : ∀ i c, Rd_entry_d i c Q → ∃ X R, Smdl_d I c X R
  map_function : M.IsSetFunction I G
  map_domain : M.IsDomainOf I T G
  elementary : ∀ i j f c X R d Y S, It_map_d G i j f → Rd_entry_d i c Q → Rd_entry_d j d Q →
    Smdl_d I c X R → Smdl_d I d Y S → Smap_d I ω c d X Y f
  identity : ∀ i f, It_map_d G i i f → ∀ x y, Rd_entry_d x y f → x = y
  comp : ∀ i j k f g h, It_map_d G i j f → It_map_d G j k g → It_map_d G i k h →
    ∀ x y z, Rd_entry_d x y f → Rd_entry_d y z g → Rd_entry_d x z h

variable (hZF : M.Models ZF) {ω α T Q G : M.Domain}
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_diagram_d.model_l (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) {i : M.Domain} (hi : M.mem i α) :
    ∃ c X R, Rd_entry_d i c Q ∧ Smdl_d I c X R := by
  obtain ⟨c, hc⟩ := (h.model_domain i).mp hi
  obtain ⟨X, R, hm⟩ := h.models i c hc
  exact ⟨c, X, R, hc, hm⟩

theorem It_diagram_d.map_bound_l (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) {i j f : M.Domain}
    (hf : It_map_d G i j f) : Rd_entry_d i j T := by
  obtain ⟨r, hr, hrf⟩ := hf
  exact ⟨r, hr, (h.map_domain r).mpr ⟨f, hrf⟩⟩

theorem It_diagram_d.map_l (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) {i j : M.Domain} (hij : Rd_entry_d i j T) :
    ∃ f, It_map_d G i j f := by
  obtain ⟨r, hr, hrt⟩ := hij
  obtain ⟨f, hrf⟩ := (h.map_domain r).mp hrt
  exact ⟨f, r, hr, hrf⟩

theorem It_diagram_d.map_unique_l (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) {i j f g : M.Domain}
    (hf : It_map_d G i j f) (hg : It_map_d G i j g) : f = g := by
  obtain ⟨r, hr, hrf⟩ := hf
  obtain ⟨s, hs, hsg⟩ := hg
  exact h.map_function.2 r f g hrf ((kpair_unique_l M hZF.1 hs hr) ▸ hsg)

theorem it_comp_elementary_l {c d e X Y Z f g : M.Domain}
    (hf : Smap_d I ω c d X Y f) (hg : Smap_d I ω d e Y Z g) :
    ∃ h, Smap_d I ω c e X Z h ∧ It_comp_d f g h := by
  obtain ⟨h, hh, hs⟩ := smap_comp_l I hZF hf hg
  exact ⟨h, hh, hh.1.1.1.1, fun x z => (hs x z).trans
    ⟨And.right, fun ⟨y, hxy, hyz⟩ => ⟨hf.1.1.input_mem_of_pairMember hxy, y, hxy, hyz⟩⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 迭代树序和完整初等图列的原公式 -/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def it_pred_m {d} (T k j : Term d) : Formula 1 d := set[d] ⟪
  ⌜k⌝ₛ ∈ ⌜j⌝ₛ ∧ (∀ i, ⌜rd_entry0_m⌝ₚ(i, ⌜j⌝ₛ, ⌜T⌝ₛ) ↔ i = ⌜j⌝ₛ ∨ ⌜rd_entry0_m⌝ₚ(i, ⌜k⌝ₛ, ⌜T⌝ₛ))⟫
derive_free_closed it_pred_m
theorem it_pred_sat_l (hE : Extensional M) {d} (η : Env M d) (T k j : Term d) :
    Formula.satisfies η (it_pred_m T k j) ↔ It_pred_d (T.eval η) (k.eval η) (j.eval η) := by
  simp only [it_pred_m, It_pred_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_extensionalEq_iff_eq hE, rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def it_order_m {d} (α T : Term d) : Formula 1 d := set[d] ⟪
  Ord(⌜α⌝ₛ) ∧ ⌜Formula.isRelation kpair_convention_l⌝ₚ(⌜T⌝ₛ) ∧
  (∀ i j, ⌜rd_entry0_m⌝ₚ(i, j, ⌜T⌝ₛ) → i ∈ ⌜α⌝ₛ ∧ j ∈ ⌜α⌝ₛ) ∧
  (∀ i ∈ ⌜α⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, i, ⌜T⌝ₛ)) ∧
  (∀ i j k, ⌜rd_entry0_m⌝ₚ(i, j, ⌜T⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j, k, ⌜T⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i, k, ⌜T⌝ₛ)) ∧
  (∀ i j, ⌜rd_entry0_m⌝ₚ(i, j, ⌜T⌝ₛ) → i = j ∨ i ∈ j) ∧
  (∀ i j k, ⌜rd_entry0_m⌝ₚ(i, k, ⌜T⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j, k, ⌜T⌝ₛ) →
    ⌜rd_entry0_m⌝ₚ(i, j, ⌜T⌝ₛ) ∨ ⌜rd_entry0_m⌝ₚ(j, i, ⌜T⌝ₛ)) ∧
  (∀ i j, j ∈ ⌜α⌝ₛ → ⌜KP.succ0_m⌝ₚ(j, i) → ∃ k, ⌜it_pred_m⌝ₚ(⌜T⌝ₛ, k, j)) ∧
  (∀ δ, δ ∈ ⌜α⌝ₛ → ⌜Formula.isLimitOrdinal⌝ₚ(δ) → ∀ i ∈ δ,
    ∃ j ∈ δ, ⌜rd_entry0_m⌝ₚ(j, δ, ⌜T⌝ₛ) ∧ (i = j ∨ i ∈ j))⟫
derive_free_closed it_order_m
theorem it_order_sat_l (hKP : M.Models KP) {d} (η : Env M d) (α T : Term d) :
    Formula.satisfies η (it_order_m α T) ↔ It_order_d (α.eval η) (T.eval η) := by
  simp only [it_order_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_mem_iff, Formula.satisfies_disj_iff,
    Formula.satisfies_isOrdinal_iff, Formula.satisfies_isLimitOrdinal_iff,
    Formula.satisfies_extensionalEq_iff_eq hKP.1, Formula.satisfies_isRelation_iff (kp_pair_l hKP),
    rd_entry0_sat_l hKP.1, KP.succ0_sat_l hKP.1, it_pred_sat_l hKP.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩,
    fun h => ⟨h.ordinal, h.relation, h.bound, h.refl, h.trans, h.forward, h.chain, h.predecessor, h.cofinal⟩⟩

def it_diagram_m {d} (ω α T Q G : Term d) : Formula 1 d := set[d] ⟪
  ⌜it_order_m⌝ₚ(⌜α⌝ₛ, ⌜T⌝ₛ) ∧ ⌜Formula.isFunction kpair_convention_l⌝ₚ(⌜Q⌝ₛ) ∧
  ⌜Formula.isDomain kpair_convention_l⌝ₚ(⌜α⌝ₛ, ⌜Q⌝ₛ) ∧
  (∀ i c, ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) → ∃ X R, ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, R)) ∧
  ⌜Formula.isFunction kpair_convention_l⌝ₚ(⌜G⌝ₛ) ∧ ⌜Formula.isDomain kpair_convention_l⌝ₚ(⌜T⌝ₛ, ⌜G⌝ₛ) ∧
  (∀ i j f c X R d Y S, ⌜it_map_m⌝ₚ(⌜G⌝ₛ, i, j, f) → ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) → ⌜rd_entry0_m⌝ₚ(j, d, ⌜Q⌝ₛ) →
    ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(c, X, R) → ⌜smdl_m (𝒞 := kpair_convention_l)⌝ₚ(d, Y, S) →
    ⌜smap_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, c, d, X, Y, f)) ∧
  (∀ i f, ⌜it_map_m⌝ₚ(⌜G⌝ₛ, i, i, f) → ∀ x y, ⌜rd_entry0_m⌝ₚ(x, y, f) → x = y) ∧
  (∀ i j k f g h, ⌜it_map_m⌝ₚ(⌜G⌝ₛ, i, j, f) → ⌜it_map_m⌝ₚ(⌜G⌝ₛ, j, k, g) → ⌜it_map_m⌝ₚ(⌜G⌝ₛ, i, k, h) →
    ∀ x y z, ⌜rd_entry0_m⌝ₚ(x, y, f) → ⌜rd_entry0_m⌝ₚ(y, z, g) → ⌜rd_entry0_m⌝ₚ(x, z, h))⟫
derive_free_closed it_diagram_m
theorem it_diagram_sat_l (hZF : M.Models ZF) {d} (η : Env M d) (ω α T Q G : Term d) :
    Formula.satisfies η (it_diagram_m ω α T Q G) ↔
      It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval η) (α.eval η) (T.eval η) (Q.eval η) (G.eval η) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [it_diagram_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_imp_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
    Formula.satisfies_isFunction_iff I hZF.1, Formula.satisfies_isDomain_iff I,
    rd_entry0_sat_l hZF.1, it_map_sat_l hZF.1, smdl_sat_l I, smap_sat_l I hZF.1,
    it_order_sat_l (ZF.modelsKP hZF), Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩,
    fun h => ⟨h.order, h.model_function, h.model_domain, h.models, h.map_function, h.map_domain, h.elementary, h.identity, h.comp⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! `It_comp_d` 本身已经是有限序列逐项改码所需的关系复合。
只要给出当前有序对解释与 `KPair_d` 的语义识别，就能直接生成
`Fseq_recode_d`，无需额外假设全局双射。 -/
namespace YesMetaZFC.SetTheory.LargeCardinal

open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

theorem It_comp_d.fseq_recode_l
    (I : kpair_convention_l.Interpretation M)
    {f g h : M.Domain}
    (codes : ∀ p a b, I.Codes p a b ↔ KPair_d M p a b)
    (comp : It_comp_d f g h) :
    Fseq_recode_d I g f h := by
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨a, b, hab⟩ := comp.1 p hp
    exact ⟨a, b, (codes p a b).mpr hab⟩
  · intro i y
    constructor
    · rintro ⟨p, hpy, hp⟩
      obtain ⟨x, hix, hxy⟩ := (comp.2 i y).mp ⟨p, (codes p i y).mp hpy, hp⟩
      obtain ⟨p₁, hpi, hp₁⟩ := hix
      obtain ⟨p₂, hpx, hp₂⟩ := hxy
      exact ⟨x, ⟨p₁, (codes p₁ i x).mpr hpi, hp₁⟩,
        ⟨p₂, (codes p₂ x y).mpr hpx, hp₂⟩⟩
    · rintro ⟨x, ⟨p₁, hpi, hp₁⟩, ⟨p₂, hpx, hp₂⟩⟩
      obtain ⟨p, hpy, hp⟩ := (comp.2 i y).mpr
        ⟨x, ⟨p₁, (codes p₁ i x).mp hpi, hp₁⟩,
          ⟨p₂, (codes p₂ x y).mp hpx, hp₂⟩⟩
      exact ⟨p, (codes p i y).mpr hpy, hp⟩

theorem It_comp_d.fseq_recode_kp_l
    (hKP : M.Models KP) {f g h : M.Domain} (comp : It_comp_d f g h) :
    Fseq_recode_d (kp_pair_l hKP) g f h := by
  exact It_comp_d.fseq_recode_l (kp_pair_l hKP) (fun _ _ _ => Iff.rfl) comp

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 整条有限树枝的联合初等尝试

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

/-- 统一尝试枚举的逐行可数性出口。 -/
theorem Ja_enum_d.row_countable_l
    {ω α Q E i e c X R : M.Domain} (en : Ja_enum_d I ω α Q E)
    (he : Rd_entry_d i e E) (hc : Rd_entry_d i c Q) (mx : KPair_d M c X R) :
    Fn0_d ω X e ∧ ∀ x, M.mem x X → ∃ n, M.mem n ω ∧ Rd_entry_d n x e :=
  en.rows i e c X R he hc mx

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

/-- 实际有限序列空间和双边真值证书检验全部内部公式。 -/
def ja_elementary_m {d} (ω X R Y W e k p : Term d) : Formula 1 d := set[d] ⟪
  ∃ Q J K, ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, ⌜ω⌝ₛ, Q) ∧
    ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, J) ∧
    ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, ⌜Y⌝ₛ, K) ∧
    ⌜at_elementary_m⌝ₚ(⌜ω⌝ₛ, ⌜X⌝ₛ, ⌜R⌝ₛ, ⌜Y⌝ₛ, ⌜W⌝ₛ, ⌜e⌝ₛ, ⌜k⌝ₛ, ⌜p⌝ₛ, Q, J, K)⟫
derive_free_closed ja_elementary_m

theorem ja_elementary_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω X R Y W e k p : Term d)
    (hω : M.IsOmega (ω.eval ρ)) (hk : M.mem (k.eval ρ) (ω.eval ρ)) :
    Formula.satisfies ρ (ja_elementary_m ω X R Y W e k p) ↔
      At_elementary_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (X.eval ρ) (R.eval ρ)
        (Y.eval ρ) (W.eval ρ) (e.eval ρ) (k.eval ρ) (p.eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [ja_elementary_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    fseq_space_sat_l I hZF.1, Definitional.Term.eval_weaken]
  let w (t : Term d) := t.weaken.weaken.weaken
  have read Q J K (hQ : Fseq_space_d I (ω.eval ρ) (ω.eval ρ) Q)
      (hJ : Fseq_space_d I (ω.eval ρ) (X.eval ρ) J) (hK : Fseq_space_d I (ω.eval ρ) (Y.eval ρ) K) :=
    at_elementary_sat_l hZF (((ρ.push Q).push J).push K)
      (w ω) (w X) (w R) (w Y) (w W) (w e) (w k) (w p) (.bound 2) (.bound 1) .newest
      (by simpa only [w, Definitional.Term.eval_weaken] using hω)
      (by simpa only [w, Definitional.Term.eval_weaken] using hk)
      (by simpa only [w, Definitional.Term.eval_weaken, Term.eval_bound_two_push,
        Term.eval_bound_one_push, Term.eval_bound_zero_push] using hQ)
      (by simpa only [w, Definitional.Term.eval_weaken, Term.eval_bound_one_push, Term.eval_bound_zero_push] using hJ)
      (by simpa only [w, Definitional.Term.eval_weaken, Definitional.Term.eval_newest] using hK)
  simp only [w, Definitional.Term.eval_weaken] at read
  constructor
  · rintro ⟨Q, J, K, hQ, hJ, hK, h⟩
    exact (read Q J K hQ hJ hK).mp h
  · intro h
    obtain ⟨Q, hQ⟩ := ZF.fseq_space_exists_l I hZF hω (ω.eval ρ)
    obtain ⟨J, hJ⟩ := ZF.fseq_space_exists_l I hZF hω (X.eval ρ)
    obtain ⟨K, hK⟩ := ZF.fseq_space_exists_l I hZF hω (Y.eval ρ)
    exact ⟨Q, J, K, hQ, hJ, hK, (read Q J K hQ hJ hK).mpr h⟩

def ja_rows_m {d} (ω Q E Y W k P : Term d) : Formula 1 d := set[d] ⟪
  ∀ i p c X R e, ⌜rd_entry0_m⌝ₚ(i, p, ⌜P⌝ₛ) → ⌜rd_entry0_m⌝ₚ(i, c, ⌜Q⌝ₛ) →
    ⌜kpair0_m⌝ₚ(c, X, R) → ⌜rd_entry0_m⌝ₚ(i, e, ⌜E⌝ₛ) →
    ⌜fn0_m⌝ₚ(⌜k⌝ₛ, ⌜Y⌝ₛ, p) ∧ ⌜at_coherent_m⌝ₚ(⌜k⌝ₛ, X, ⌜Y⌝ₛ, e, p) ∧
      ⌜ja_elementary_m⌝ₚ(⌜ω⌝ₛ, X, R, ⌜Y⌝ₛ, ⌜W⌝ₛ, e, ⌜k⌝ₛ, p)⟫
derive_free_closed ja_rows_m

theorem ja_rows_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω Q E Y W k P : Term d)
    (hω : M.IsOmega (ω.eval ρ)) (hk : M.mem (k.eval ρ) (ω.eval ρ)) :
    Formula.satisfies ρ (ja_rows_m ω Q E Y W k P) ↔
      Ja_rows_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (Q.eval ρ) (E.eval ρ)
        (Y.eval ρ) (W.eval ρ) (k.eval ρ) (P.eval ρ) := by
  simp only [ja_rows_m, Ja_rows_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    rd_entry0_sat_l hZF.1, kpair0_sat_l hZF.1, Formula.satisfies_conj_iff, fn0_sat_l hZF.1,
    at_coherent_sat_l hZF.1, Definitional.Term.eval_weaken]
  simp only [ja_elementary_sat_l hZF, Definitional.Term.eval_weaken, hω, hk]
  rfl

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
      ⌜kpair0_m⌝ₚ(c, X, R) → ⌜rd_entry0_m⌝ₚ(⌜z⌝ₛ, e, ⌜E⌝ₛ) →
        ⌜at_prescribed_m⌝ₚ(⌜k⌝ₛ, X, ⌜Y⌝ₛ, e, ⌜π⌝ₛ, p)) ∧ ⌜ja_commute_m⌝ₚ(⌜G⌝ₛ, ⌜E⌝ₛ, ⌜P⌝ₛ)⟫
derive_free_closed ja_node_m

theorem ja_node_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω T Q G E Y W z π k P : Term d)
    (hω : M.IsOmega (ω.eval ρ)) :
    Formula.satisfies ρ (ja_node_m ω T Q G E Y W z π k P) ↔
      Ja_node_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (T.eval ρ) (Q.eval ρ) (G.eval ρ) (E.eval ρ) (Y.eval ρ) (W.eval ρ)
        (z.eval ρ) (π.eval ρ) (k.eval ρ) (P.eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [ja_node_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isFunction_iff I hZF.1, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_exists_iff, rd_entry0_sat_l hZF.1, Formula.satisfies_imp_iff,
    kpair0_sat_l hZF.1, at_prescribed_sat_l hZF.1, ja_commute_sat_l hZF.1, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, (ja_rows_sat_l hZF _ _ _ _ _ _ _ _ hω a).mp d, e, f⟩,
    fun h => ⟨h.length, h.function, h.domain,
      (ja_rows_sat_l hZF _ _ _ _ _ _ _ _ hω h.length).mpr h.rows, h.root, h.commute⟩⟩

def ja_extend_m {d} (T s t : Term d) : Formula 1 d := set[d] ⟪
  ∃ k P l Q, ⌜kpair0_m⌝ₚ(⌜s⌝ₛ, k, P) ∧ ⌜kpair0_m⌝ₚ(⌜t⌝ₛ, l, Q) ∧ k ∈ l ∧
    ⌜rd_entry0_m⌝ₚ(k, l, ⌜T⌝ₛ) ∧ (∀ i p q, ⌜rd_entry0_m⌝ₚ(i, p, P) → ⌜rd_entry0_m⌝ₚ(i, q, Q) → p ⊆ q)⟫
derive_free_closed ja_extend_m

theorem ja_extend_sat_l (hE : Extensional M) {d} (ρ : Env M d) (T s t : Term d) :
    Formula.satisfies ρ (ja_extend_m T s t) ↔ Ja_extend_d (T.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [ja_extend_m, Ja_extend_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hE, Formula.satisfies_mem_iff, rd_entry0_sat_l hE, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从末结点嵌入实际构造联合尝试节点

每一行由原树嵌入、末结点嵌入及既有枚举复合，再截取有限定义域。
各行的图唯一，替代一次收集全部前驱；没有选择嵌入的额外参数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def Ja_value_d (G E k j i a y : M.Domain) : Prop := ∃ e f x v,
  Rd_entry_d i e E ∧ It_map_d G i k f ∧ Rd_entry_d a x e ∧ Rd_entry_d x v f ∧ Rd_entry_d v y j

def ja_value_m {d} (G E k j i a y : Term d) : Formula 1 d := set[d] ⟪
  ∃ e f x v, ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, e, ⌜E⌝ₛ) ∧ ⌜it_map_m⌝ₚ(⌜G⌝ₛ, ⌜i⌝ₛ, ⌜k⌝ₛ, f) ∧
    ⌜rd_entry0_m⌝ₚ(⌜a⌝ₛ, x, e) ∧ ⌜rd_entry0_m⌝ₚ(x, v, f) ∧ ⌜rd_entry0_m⌝ₚ(v, ⌜y⌝ₛ, ⌜j⌝ₛ)⟫
derive_free_closed ja_value_m

theorem ja_value_sat_l (hE : Extensional M) {d} (ρ : Env M d) (G E k j i a y : Term d) :
    Formula.satisfies ρ (ja_value_m G E k j i a y) ↔
      Ja_value_d (G.eval ρ) (E.eval ρ) (k.eval ρ) (j.eval ρ) (i.eval ρ) (a.eval ρ) (y.eval ρ) := by
  simp only [ja_value_m, Ja_value_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    rd_entry0_sat_l hE, it_map_sat_l hE, Definitional.Term.eval_weaken]; rfl

private def ja_lift_m {d} (G E k j Y i p : Term d) : Formula 1 d := set[d] ⟪
  ⌜fn0_m⌝ₚ(⌜k⌝ₛ, ⌜Y⌝ₛ, ⌜p⌝ₛ) ∧ (∀ a y, ⌜rd_entry0_m⌝ₚ(a, y, ⌜p⌝ₛ) ↔
    a ∈ ⌜k⌝ₛ ∧ ⌜ja_value_m⌝ₚ(⌜G⌝ₛ, ⌜E⌝ₛ, ⌜k⌝ₛ, ⌜j⌝ₛ, ⌜i⌝ₛ, a, y))⟫
derive_free_closed ja_lift_m

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ja_node_of_l {ω α T Q G E Y W z π k c X R d j : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω α T Q G) (en : Ja_enum_d I ω α Q E)
    (hk : M.mem k ω) (hc : Rd_entry_d k c Q) (mx : Smdl_d I c X R) (my : Smdl_d I d Y W)
    (hj : Smap_d I ω c d X Y j)
    (root : ∀ x y, Rd_entry_d x y π → ∃ f v, It_map_d G z k f ∧ Rd_entry_d x v f ∧ Rd_entry_d v y j) :
    ∃ P, Ja_node_d I ω T Q G E Y W z π k P ∧
      ∀ i p, Rd_entry_d i p P → ∀ a y, Rd_entry_d a y p ↔ M.mem a k ∧ Ja_value_d G E k j i a y := by
  let θ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  obtain ⟨B, bs⟩ := ZF.separation_exists_d hZF θ ⟨Fin.cases k (fun _ => T), fun _ => k⟩ α
  have pred i : M.mem i B ↔ Rd_entry_d i k T := by
    have b : M.mem i B ↔ M.mem i α ∧ Rd_entry_d i k T := by
      simpa only [θ, UnarySchema.denote, rd_entry0_sat_l hZF.1] using! bs i
    exact b.trans ⟨And.right, fun hi => ⟨(h.order.bound i k hi).1, hi⟩⟩
  obtain ⟨S, space⟩ := ZF.exists_functionSpace hZF I k Y
  let φ : BinarySchema 5 := { body := ja_lift_m (.bound 4) (.bound 5) (.bound 2) (.bound 6) (.bound 3) (.bound 1) .newest }
  let ρ : Env M 5 := ⟨Fin.cases k (Fin.cases Y (Fin.cases G (Fin.cases E (fun _ => j)))), fun _ => k⟩
  have sat i p : φ.denote ρ i p ↔ Fn0_d k Y p ∧
      ∀ a y, Rd_entry_d a y p ↔ M.mem a k ∧ Ja_value_d G E k j i a y := by
    simp only [φ, ja_lift_m, BinarySchema.denote, Formula.satisfies_conj_iff, fn0_sat_l hZF.1,
      Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, rd_entry0_sat_l hZF.1,
      Formula.satisfies_mem_iff, ja_value_sat_l hZF.1]; rfl
  have full i b A V e f (hb : Rd_entry_d i b Q) (ma : Smdl_d I b A V)
      (he : Rd_entry_d i e E) (hf : It_map_d G i k f) :
      ∃ v, Smap_d I ω b d A Y v ∧ It_comp_d f j v ∧ ∀ a y,
        Ja_value_d G E k j i a y ↔ ∃ x, Rd_entry_d a x e ∧ Rd_entry_d x y v := by
    obtain ⟨v, hv, vs⟩ := it_comp_elementary_l hZF (h.elementary i k f b A V c X R hf hb hc ma mx) hj
    refine ⟨v, hv, vs, fun a y => ⟨?_, ?_⟩⟩
    · rintro ⟨e', f', x, t, he', hf', hax, hxt, hty⟩
      exact ⟨x, en.function.2 i e' e he' he ▸ hax,
        (vs.2 x y).mpr ⟨t, h.map_unique_l hZF hf' hf ▸ hxt, hty⟩⟩
    · rintro ⟨x, hax, hxy⟩
      obtain ⟨t, hxt, hty⟩ := (vs.2 x y).mp hxy
      exact ⟨e, f, x, t, he, hf, hax, hxt, hty⟩
  have total i (hi : M.mem i B) : ∃ p, φ.denote ρ i p := by
    have hi := (pred i).mp hi
    obtain ⟨b, A, V, hb, ma⟩ := h.model_l hZF (h.order.bound i k hi).1
    obtain ⟨e, he⟩ := (en.domain i).mp (h.order.bound i k hi).1
    obtain ⟨f, hf⟩ := h.map_l hZF hi
    obtain ⟨v, hv, _, vs⟩ := full i b A V e f hb ma he hf
    have ef := (en.rows i e b A V he hb ma.1).1
    obtain ⟨q, hq⟩ := cp0_exists_l (ZF.modelsKP hZF) ef (fn0_of_function_l (ZF.modelsKP hZF) hv.1.1)
    obtain ⟨p, hp⟩ := ZF.exists_restriction hZF I q k
    have pf := hp.isSetFunctionFromTo (fn0_function_l (ZF.modelsKP hZF) hq.1) (hω.transitive (ZF.modelsKP hZF) k hk)
    refine ⟨p, (sat i p).mpr ⟨fn0_of_function_l (ZF.modelsKP hZF) pf, fun a y => ?_⟩⟩
    refine (hp.2 a y).trans (and_congr_right fun ha => ?_)
    obtain ⟨x, _, hax⟩ := ef.2.1 a (hω.transitive (ZF.modelsKP hZF) k hk a ha)
    refine (hq.value_l ef (fn0_of_function_l (ZF.modelsKP hZF) hv.1.1) hax).trans ⟨fun hxy => (vs a y).mpr ⟨x, hax, hxy⟩, ?_⟩
    intro hy
    obtain ⟨x', hax', hxy⟩ := (vs a y).mp hy
    exact (fn0_function_l (ZF.modelsKP hZF) ef).1.2 a x' x hax' hax ▸ hxy
  have unique i p q (hp : φ.denote ρ i p) (hq : φ.denote ρ i q) : p = q := by
    obtain ⟨pf, ps⟩ := (sat i p).mp hp
    obtain ⟨qf, qs⟩ := (sat i q).mp hq
    exact pf.ext_l hZF.1 qf (fun a ha => (pf.2.1 a ha).elim fun y hy =>
      ⟨y, hy.2, (qs a y).mpr ((ps a y).mp hy.2)⟩)
  obtain ⟨P, pf, ps⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total
    (fun i _ => unique i) (fun i p _ hp => (space p).mpr (fn0_function_l (ZF.modelsKP hZF) ((sat i p).mp hp).1))
  have entry i p (hi : Rd_entry_d i p P) := (sat i p).mp ((ps i p).mp hi).2
  have dom i : (∃ p, Rd_entry_d i p P) ↔ Rd_entry_d i k T := (pf.2.1 i).symm.trans (pred i)
  have part i p b A V e f v (hi : Rd_entry_d i p P) (hb : Rd_entry_d i b Q)
      (ma : Smdl_d I b A V) (he : Rd_entry_d i e E) (hf : It_map_d G i k f)
      (hv : Smap_d I ω b d A Y v) (vs : It_comp_d f j v) : Cp0_d k A Y e v p := by
    refine ⟨(entry i p hi).1, fun a ha => ?_⟩
    obtain ⟨x, hx, hax⟩ := (en.rows i e b A V he hb ma.1).1.2.1 a (hω.transitive (ZF.modelsKP hZF) k hk a ha)
    obtain ⟨y, hy, hxy⟩ := hv.1.1.2.2 x hx
    obtain ⟨t, hxt, hty⟩ := (vs.2 x y).mp hxy
    exact ⟨x, hx, y, hy, hax, hxy, (entry i p hi).2 a y |>.mpr ⟨ha, e, f, x, t, he, hf, hax, hxt, hty⟩⟩
  have rows : Ja_rows_d I ω Q E Y W k P := by
    intro i p b A V e hi hb hp he
    obtain ⟨A', V', ma⟩ := h.models i b hb
    obtain ⟨ea, ev⟩ := kpair_injective_l M ma.1 hp
    subst A' V'
    obtain ⟨f, hf⟩ := h.map_l hZF ((dom i).mp ⟨p, hi⟩)
    obtain ⟨v, hv, vs, _⟩ := full i b A V e f hb ma he hf
    obtain ⟨o, ho⟩ := KP.exists_empty (ZF.modelsKP hZF)
    have node := at_node_of_l hZF hω ma my hv (en.rows i e b A V he hb ma.1).1
      (τ := o) (fun _ _ ⟨r, _, hr⟩ => (ho r hr).elim) hk (part i p b A V e f v hi hb ma he hf hv vs)
    exact ⟨node.function, node.coherent, node.elementary⟩
  refine ⟨P, ⟨hk, pf.1, dom, rows, ?_, ?_⟩, fun i p hi => (entry i p hi).2⟩
  · intro p b A V e hp _ _ he a ha x _ y _ hax hxy
    obtain ⟨f, v, hf, hxv, hvy⟩ := root x y hxy
    exact ((entry z p hp).2 a y).mpr ⟨ha, e, f, x, v, he, hf, hax, hxv, hvy⟩
  · intro i l p q e f g a b x y u v hp hq he hf hg hax hby hxy hau hbv
    obtain ⟨_, e', fi, x', s, he', hfi, hax', hxs, hsu⟩ := ((entry i p hp).2 a u).mp hau
    obtain ⟨_, f', fl, y', t, hf', hfl, hby', hyt, htv⟩ := ((entry l q hq).2 b v).mp hbv
    obtain ⟨ci, A, U, hci, ma⟩ := h.model_l hZF (h.order.bound i k ((dom i).mp ⟨p, hp⟩)).1
    obtain ⟨cl, C, V, hcl, mb⟩ := h.model_l hZF (h.order.bound l k ((dom l).mp ⟨q, hq⟩)).1
    have xe := (fn0_function_l (ZF.modelsKP hZF) (en.rows i e ci A U he hci ma.1).1).1.2 a x' x
      (en.function.2 i e' e he' he ▸ hax') hax
    have ye := (fn0_function_l (ZF.modelsKP hZF) (en.rows l f cl C V hf hcl mb.1).1).1.2 b y' y
      (en.function.2 l f' f hf' hf ▸ hby') hby
    have hxt := h.comp i l k g fl fi hg hfl hfi x y t hxy (ye ▸ hyt)
    have eq := (h.elementary i k fi ci A U c X R hfi hci hc ma mx).1.1.1.2 x s t (xe ▸ hxs) hxt
    exact hj.1.1.1.2 t u v (eq ▸ hsu) htv

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 联合尝试的实际节点集与严格扩展关系

有限行属于既有有限序列空间，行图属于其与 ω 的积的幂集。
据此用分离得到全部节点；严格扩展反向存为下降关系，供内部良基秩使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Ja_cell_d (ω T Q G E Y W z π s : M.Domain) : Prop :=
  ∃ k P, KPair_d M s k P ∧ Ja_node_d I ω T Q G E Y W z π k P

def ja_cell_m {d} (ω T Q G E Y W z π s : Term d) : Formula 1 d := set[d] ⟪
  ∃ k P, ⌜kpair0_m⌝ₚ(⌜s⌝ₛ, k, P) ∧
    ⌜ja_node_m⌝ₚ(⌜ω⌝ₛ, ⌜T⌝ₛ, ⌜Q⌝ₛ, ⌜G⌝ₛ, ⌜E⌝ₛ, ⌜Y⌝ₛ, ⌜W⌝ₛ, ⌜z⌝ₛ, ⌜π⌝ₛ, k, P)⟫
derive_free_closed ja_cell_m

theorem ja_cell_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (ω T Q G E Y W z π s : Term d)
    (hω : M.IsOmega (ω.eval ρ)) :
    Formula.satisfies ρ (ja_cell_m ω T Q G E Y W z π s) ↔
      Ja_cell_d (kp_pair_l (ZF.modelsKP hZF)) (ω.eval ρ) (T.eval ρ) (Q.eval ρ) (G.eval ρ) (E.eval ρ) (Y.eval ρ) (W.eval ρ)
        (z.eval ρ) (π.eval ρ) (s.eval ρ) := by
  simp only [ja_cell_m, Ja_cell_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    kpair0_sat_l hZF.1, ja_node_sat_l hZF, Definitional.Term.eval_weaken, hω]; rfl

structure Ja_space_d (ω T Q G E Y W z π A R : M.Domain) : Prop where
  nodes : ∀ s, M.mem s A ↔ Ja_cell_d I ω T Q G E Y W z π s
  relation : M.IsSetRelation I R
  edges : ∀ s t, Rd_entry_d t s R ↔ M.mem s A ∧ M.mem t A ∧ Ja_extend_d T s t

variable (hZF : M.Models ZF)
local notation "I₀" => kp_pair_l (ZF.modelsKP hZF)

theorem Ja_space_d.node_l {ω T Q G E Y W z π A R s k P : M.Domain}
    (h : Ja_space_d I₀ ω T Q G E Y W z π A R) (hs : M.mem s A) (hp : KPair_d M s k P) :
    Ja_node_d I₀ ω T Q G E Y W z π k P := by
  obtain ⟨l, Q', hq, node⟩ := (h.nodes s).mp hs
  obtain ⟨el, eq⟩ := kpair_injective_l M hq hp
  subst l Q'
  exact node

theorem Ja_extend_d.read_l {T s t k P l Q : M.Domain} (e : Ja_extend_d T s t)
    (hs : KPair_d M s k P) (ht : KPair_d M t l Q) : M.mem k l ∧ Rd_entry_d k l T ∧
      ∀ i p q, Rd_entry_d i p P → Rd_entry_d i q Q → M.MemberSubset p q := by
  obtain ⟨k', P', l', Q', hs', ht', hk, hr, sub⟩ := e
  obtain ⟨ek, ep⟩ := kpair_injective_l M hs' hs
  obtain ⟨el, eq⟩ := kpair_injective_l M ht' ht
  subst k' P' l' Q'
  exact ⟨hk, hr, sub⟩

theorem ja_space_l {ω T Q G E Y W z π : M.Domain}
    (hω : M.IsOmega ω) (h : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G) (en : Ja_enum_d I₀ ω ω Q E) :
    ∃ A R, Ja_space_d I₀ ω T Q G E Y W z π A R := by
  obtain ⟨S, hs⟩ := ZF.fseq_space_exists_l I₀ hZF hω Y
  obtain ⟨D, hd⟩ := ZF.exists_cartesianProduct hZF I₀ ω S
  obtain ⟨V, hv⟩ := ZF.exists_powerSet hZF D
  obtain ⟨U, hu⟩ := ZF.exists_cartesianProduct hZF I₀ ω V
  let φ : UnarySchema 9 := { body := (ja_cell_m (.bound 1) (.bound 2) (.bound 3) (.bound 4)
    (.bound 5) (.bound 6) (.bound 7) (.bound 8) (.bound 9) .newest) }
  let ρ : Env M 9 := ⟨Fin.cases ω (Fin.cases T (Fin.cases Q (Fin.cases G (Fin.cases E
    (Fin.cases Y (Fin.cases W (Fin.cases z (fun _ => π)))))))), fun _ => ω⟩
  have sat s : φ.denote ρ s ↔ Ja_cell_d I₀ ω T Q G E Y W z π s := ja_cell_sat_l hZF _ _ _ _ _ _ _ _ _ _ _ hω
  have bound s (snode : Ja_cell_d I₀ ω T Q G E Y W z π s) : M.mem s U := by
    obtain ⟨k, P, hp, node⟩ := snode
    refine (hu s).mpr ⟨k, node.length, P, (hv P).mpr ?_, hp⟩
    intro r hr
    obtain ⟨i, p, hi⟩ := node.function.1 r hr
    have hip : Rd_entry_d i p P := ⟨r, hi, hr⟩
    have hiω := (h.order.bound i k ((node.domain i).mp ⟨p, hip⟩)).1
    obtain ⟨c, X, R, hc, mx⟩ := h.model_l hZF hiω
    obtain ⟨e, he⟩ := (en.domain i).mp hiω
    exact (hd r).mpr ⟨i, hiω, p, (hs p).mpr ⟨k, node.length,
      fn0_function_l (ZF.modelsKP hZF) (node.rows i p c X R e hip hc mx.1 he).1⟩, hi⟩
  obtain ⟨A, ha⟩ := ZF.separation_exists_d hZF φ ρ U
  have nodes s : M.mem s A ↔ Ja_cell_d I₀ ω T Q G E Y W z π s :=
    (ha s).trans ⟨fun h => (sat s).mp h.2, fun h => ⟨bound s h, (sat s).mpr h⟩⟩
  let ψ : BinarySchema 1 := { body := ja_extend_m (.bound 2) .newest (.bound 1) }
  obtain ⟨R, hr, rs⟩ := ZF.exists_setRelationOn_of_denote hZF I₀ ψ ⟨fun _ => T, fun _ => T⟩ A
  exact ⟨A, R, nodes, hr.1, fun s t => (rs t s).trans
    ⟨fun h => ⟨h.2.1, h.1, (ja_extend_sat_l hZF.1 ..).mp h.2.2⟩,
      fun h => ⟨h.2.1, h.1, (ja_extend_sat_l hZF.1 ..).mpr h.2.2⟩⟩⟩

/-- 扩展的传递性同时使用树序传递性与中间节点的全部前驱行。 -/
theorem ja_extend_trans_l {ω T Q G E Y W z π s t u : M.Domain} (h : It_order_d ω T)
    (ns : Ja_cell_d I₀ ω T Q G E Y W z π s) (nt : Ja_cell_d I₀ ω T Q G E Y W z π t)
    (nu : Ja_cell_d I₀ ω T Q G E Y W z π u) (st : Ja_extend_d T s t) (tu : Ja_extend_d T t u) : Ja_extend_d T s u := by
  obtain ⟨k, P, hp, np⟩ := ns
  obtain ⟨l, Q', hq, nq⟩ := nt
  obtain ⟨m, V, hv, nv⟩ := nu
  obtain ⟨k', P', l', Q'', hp', hq', hkl, ktl, sub⟩ := st
  obtain ⟨ek, ep⟩ := kpair_injective_l M hp' hp
  obtain ⟨el, eq⟩ := kpair_injective_l M hq' hq
  subst k' P' l' Q''
  obtain ⟨l', Q'', m', V', hq', hv', hlm, ltm, sub'⟩ := tu
  obtain ⟨el, eq⟩ := kpair_injective_l M hq' hq
  obtain ⟨em, ev⟩ := kpair_injective_l M hv' hv
  subst l' Q'' m' V'
  refine ⟨k, P, m, V, hp, hv, (h.ordinal.mem nv.length).transitive l hlm k hkl,
    h.trans k l m ktl ltm, fun i p r hip hir => ?_⟩
  obtain ⟨q, hiq⟩ := (nq.domain i).mpr (h.trans i k l ((np.domain i).mp ⟨p, hip⟩) ktl)
  exact fun x hx => sub' i q r hiq hir x (sub i p q hip hiq x hx)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 联合尝试节点在实际工作源中的绝对性

有限列、有限程序和双边真值证书均实际属于源。无界量词通过图的坐标
与源的有限闭性回收，故不需要把任意一阶真值假定为绝对。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.sequences_relative_l {ω κ K Z S : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z S) (nz : Nonempty {x // M.mem x Z})
    {d} (ρ : Env (rt_model_l Z nz) d) (w A Q : Term d) (hw : (w.eval ρ).val = ω) :
    Formula.satisfies ρ (fseq_space_m (𝒞 := kpair_convention_l) w A Q) ↔
      Fseq_space_d I ω (A.eval ρ).val (Q.eval ρ).val := by
  let J := rt_pair_l source.transitive nz hZF.1 (source.algebra_l (ZF.modelsKP hZF)).pair
  have tr (f a b : (rt_model_l Z nz).Domain) : (rt_model_l Z nz).IsSetFunctionFromTo J f a b ↔
      M.IsSetFunctionFromTo I f.val a.val b.val :=
    rt_function_from_l source.transitive nz hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
      (source.algebra_l (ZF.modelsKP hZF)).pair f a b
  simp only [fseq_space_m, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isFunctionFromTo_iff J (rt_model_ext_l hZF.1 source.transitive nz), tr,
    Definitional.Term.eval_weaken]
  obtain ⟨c, code⟩ := source.code
  constructor
  · intro h f
    constructor
    · intro hf
      obtain ⟨n, hn, fn⟩ := (h ⟨f, source.transitive _ (Q.eval ρ).property f hf⟩).mp hf
      exact ⟨n.val, hw ▸ hn, fn⟩
    · rintro ⟨n, hn, fn⟩
      have hf := sc_finite_function_l (ZF.modelsKP hZF) source.omega source.transitive (source.algebra_l (ZF.modelsKP hZF)).pair (source.algebra_l (ZF.modelsKP hZF)).union source.omega_mem
        (source.transitive _ (A.eval ρ).property) hn (fn0_of_function_l (ZF.modelsKP hZF) fn)
      exact (h ⟨f, hf⟩).mpr ⟨⟨n, source.transitive ω source.omega_mem n hn⟩, hw ▸ hn, fn⟩
  · intro h f
    exact (h f.val).trans ⟨fun ⟨n, hn, fn⟩ =>
      ⟨⟨n, source.transitive ω source.omega_mem n hn⟩, hw ▸ hn, fn⟩,
      fun ⟨n, hn, fn⟩ => ⟨n.val, hw ▸ hn, fn⟩⟩

theorem Ep_source_d.ja_elementary_l {ω κ K Z S : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z S) (nz : Nonempty {x // M.mem x Z})
    {d} (ρ : Env (rt_model_l Z nz) d) (w A R B V e n p : Term d)
    (hw : (w.eval ρ).val = ω) (hn : M.mem (n.eval ρ).val ω) :
    Formula.satisfies ρ (ja_elementary_m w A R B V e n p) ↔
      At_elementary_d I ω (A.eval ρ).val (R.eval ρ).val (B.eval ρ).val (V.eval ρ).val
        (e.eval ρ).val (n.eval ρ).val (p.eval ρ).val := by
  simp only [ja_elementary_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    source.sequences_relative_l hZF nz, Definitional.Term.eval_weaken, hw,
    at_relative_sat_l (ZF.modelsKP hZF) source.transitive nz]
  constructor
  · rintro ⟨Q, J, L, hQ, hJ, hL, h⟩
    exact (source.at_elementary_l hZF (A.eval ρ).property (R.eval ρ).property
      (B.eval ρ).property (V.eval ρ).property hn hQ hJ hL).mp h
  · intro h
    obtain ⟨Q, hQZ, hQ⟩ := (source.sequences_l (ZF.modelsKP hZF)).1 ω source.omega_mem
    obtain ⟨J, hJZ, hJ⟩ := (source.sequences_l (ZF.modelsKP hZF)).1 (A.eval ρ).val (A.eval ρ).property
    obtain ⟨L, hLZ, hL⟩ := (source.sequences_l (ZF.modelsKP hZF)).1 (B.eval ρ).val (B.eval ρ).property
    exact ⟨⟨Q, hQZ⟩, ⟨J, hJZ⟩, ⟨L, hLZ⟩, hQ, hJ, hL,
      (source.at_elementary_l hZF (A.eval ρ).property (R.eval ρ).property
        (B.eval ρ).property (V.eval ρ).property hn hQ hJ hL).mpr h⟩

private theorem ja_map_relative_l (hE : Extensional M) {Z : M.Domain} (hZ : M.TransitiveSet Z)
    (nz : Nonempty {x // M.mem x Z}) {d} (ρ : Env (rt_model_l Z nz) d) (G i j f : Term d) :
    Formula.satisfies ρ (it_map_m G i j f) ↔ It_map_d (G.eval ρ).val (i.eval ρ).val (j.eval ρ).val (f.eval ρ).val := by
  have pair (r a b : (rt_model_l Z nz).Domain) : KPair_d (rt_model_l Z nz) r a b ↔ KPair_d M r.val a.val b.val := by
    let η : Env (rt_model_l Z nz) 3 := ⟨Fin.cases r (Fin.cases a (fun _ => b)), fun _ => r⟩
    exact (kpair0_sat_l (rt_model_ext_l hE hZ nz) η .newest (.bound 1) (.bound 2)).symm.trans
      ((rt_model_delta_l hZ nz (kpair0_delta_l ..) η).trans (kpair0_sat_l hE ..))
  rw [it_map_sat_l (rt_model_ext_l hE hZ nz)]
  exact ⟨fun ⟨r, hp, hr⟩ => ⟨r.val, (pair r _ _).mp hp, (rt_entry_l hZ nz hE ..).mp hr⟩,
    fun ⟨r, hp, hr⟩ => ⟨⟨r, (rd_entry_transitive_l hZ (G.eval ρ).property hr).1⟩,
      (pair _ _ _).mpr hp, (rt_entry_l hZ nz hE ..).mpr hr⟩⟩

theorem Ep_source_d.ja_node_l {ω κ K Z S : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z S) (nz : Nonempty {x // M.mem x Z})
    {d} (ρ : Env (rt_model_l Z nz) d) (w T Q G E Y W z π k P : Term d) (hw : (w.eval ρ).val = ω) :
    Formula.satisfies ρ (ja_node_m w T Q G E Y W z π k P) ↔
      Ja_node_d I ω (T.eval ρ).val (Q.eval ρ).val (G.eval ρ).val (E.eval ρ).val
        (Y.eval ρ).val (W.eval ρ).val (z.eval ρ).val (π.eval ρ).val (k.eval ρ).val (P.eval ρ).val := by
  have ent {a} (η : Env (rt_model_l Z nz) a) (x y f : Term a) : Formula.satisfies η (rd_entry0_m x y f) ↔
      Rd_entry_d (x.eval η).val (y.eval η).val (f.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z nz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive nz (rd_entry0_delta_l x y f) η).trans (rd_entry0_sat_l hZF.1 ..)
  have pair {a} (η : Env (rt_model_l Z nz) a) (p x y : Term a) : Formula.satisfies η (kpair0_m p x y) ↔
      KPair_d M (p.eval η).val (x.eval η).val (y.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z nz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive nz (kpair0_delta_l p x y) η).trans (kpair0_sat_l hZF.1 ..)
  have fn {a} (η : Env (rt_model_l Z nz) a) (x y f : Term a) : Formula.satisfies η (fn0_m x y f) ↔
      Fn0_d (x.eval η).val (y.eval η).val (f.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z nz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive nz (fn0_delta_l x y f) η).trans (fn0_sat_l hZF.1 ..)
  have coh {a} (η : Env (rt_model_l Z nz) a) (n A B e p : Term a) : Formula.satisfies η (at_coherent_m n A B e p) ↔
      At_coherent_d (n.eval η).val (A.eval η).val (B.eval η).val (e.eval η).val (p.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z nz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive nz (at_coherent_delta_l n A B e p) η).trans (at_coherent_sat_l hZF.1 ..)
  have pre {a} (η : Env (rt_model_l Z nz) a) (n A B e τ p : Term a) : Formula.satisfies η (at_prescribed_m n A B e τ p) ↔
      At_prescribed_d (n.eval η).val (A.eval η).val (B.eval η).val (e.eval η).val (τ.eval η).val (p.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z nz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive nz (at_prescribed_delta_l n A B e τ p) η).trans (at_prescribed_sat_l hZF.1 ..)
  have rows (hk : M.mem (k.eval ρ).val ω) : Formula.satisfies ρ (ja_rows_m w Q E Y W k P) ↔
      Ja_rows_d I ω (Q.eval ρ).val (E.eval ρ).val (Y.eval ρ).val (W.eval ρ).val (k.eval ρ).val (P.eval ρ).val := by
    simp only [ja_rows_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_conj_iff, ent, pair, fn, coh, source.ja_elementary_l hZF nz,
      Definitional.Term.eval_weaken, hw, hk]
    constructor
    · intro h i p c A R e hi hc hp he
      have ip := rd_entry_transitive_l source.transitive (P.eval ρ).property hi
      have ic := rd_entry_transitive_l source.transitive (Q.eval ρ).property hc
      have ar := hp.mem_l M source.transitive ic.2
      have ie := rd_entry_transitive_l source.transitive (E.eval ρ).property he
      exact h ⟨i, ip.1⟩ ⟨p, ip.2⟩ ⟨c, ic.2⟩ ⟨A, ar.1⟩ ⟨R, ar.2⟩ ⟨e, ie.2⟩ hi hc hp he
    · exact fun h i p c A R e => h i.val p.val c.val A.val R.val e.val
  let J := rt_pair_l source.transitive nz hZF.1 (source.algebra_l (ZF.modelsKP hZF)).pair
  have funs (f : (rt_model_l Z nz).Domain) : (rt_model_l Z nz).IsSetFunction J f ↔ M.IsSetFunction I f.val :=
    rt_function_l source.transitive nz hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) (source.algebra_l (ZF.modelsKP hZF)).pair f
  have commute : Formula.satisfies ρ (ja_commute_m G E P) ↔ Ja_commute_d (G.eval ρ).val (E.eval ρ).val (P.eval ρ).val := by
    simp only [ja_commute_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      ent, ja_map_relative_l hZF.1 source.transitive nz, Formula.satisfies_extensionalEq_iff_eq
        (rt_model_ext_l hZF.1 source.transitive nz), Definitional.Term.eval_weaken]
    constructor
    · intro h i j p q e f g u v x y a b hi hj he hf hg hux hvy hxy hua hvb
      have ip := rd_entry_transitive_l source.transitive (P.eval ρ).property hi
      have jq := rd_entry_transitive_l source.transitive (P.eval ρ).property hj
      have ie := rd_entry_transitive_l source.transitive (E.eval ρ).property he
      have jf := rd_entry_transitive_l source.transitive (E.eval ρ).property hf
      have owned : M.mem g Z := by
        obtain ⟨_, _, hr⟩ := hg
        exact (rd_entry_transitive_l source.transitive (G.eval ρ).property hr).2
      have ux := rd_entry_transitive_l source.transitive ie.2 hux
      have vy := rd_entry_transitive_l source.transitive jf.2 hvy
      have ua := rd_entry_transitive_l source.transitive ip.2 hua
      have vb := rd_entry_transitive_l source.transitive jq.2 hvb
      exact congrArg Subtype.val (h ⟨i, ip.1⟩ ⟨j, jq.1⟩ ⟨p, ip.2⟩ ⟨q, jq.2⟩ ⟨e, ie.2⟩ ⟨f, jf.2⟩
        ⟨g, owned⟩ ⟨u, ux.1⟩ ⟨v, vy.1⟩ ⟨x, ux.2⟩ ⟨y, vy.2⟩ ⟨a, ua.2⟩ ⟨b, vb.2⟩ hi hj he hf hg hux hvy hxy hua hvb)
    · exact fun h i j p q e f g u v x y a b hi hj he hf hg hux hvy hxy hua hvb =>
        Subtype.ext (h i.val j.val p.val q.val e.val f.val g.val u.val v.val x.val y.val a.val b.val hi hj he hf hg hux hvy hxy hua hvb)
  simp only [ja_node_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isFunction_iff J (rt_model_ext_l hZF.1 source.transitive nz), funs,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_imp_iff, ent, pair, pre, Definitional.Term.eval_weaken, commute]
  constructor
  · rintro ⟨hk, hf, dom, rr, root, comm⟩
    have hk : M.mem (k.eval ρ).val ω := hw ▸ hk
    refine ⟨hk, hf, fun i => ⟨?_, ?_⟩, (rows hk).mp rr, ?_, comm⟩
    · rintro ⟨p, hp⟩
      have ip := rd_entry_transitive_l source.transitive (P.eval ρ).property hp
      exact (dom ⟨i, ip.1⟩).mp ⟨⟨p, ip.2⟩, hp⟩
    · intro hi
      obtain ⟨p, hp⟩ := (dom ⟨i, (rd_entry_transitive_l source.transitive (T.eval ρ).property hi).1⟩).mpr hi
      exact ⟨p.val, hp⟩
    · intro p c A R e hp hc pair he
      have zp := rd_entry_transitive_l source.transitive (P.eval ρ).property hp
      have zc := rd_entry_transitive_l source.transitive (Q.eval ρ).property hc
      have ar := pair.mem_l M source.transitive zc.2
      exact root ⟨p, zp.2⟩ ⟨c, zc.2⟩ ⟨A, ar.1⟩ ⟨R, ar.2⟩
        ⟨e, (rd_entry_transitive_l source.transitive (E.eval ρ).property he).2⟩ hp hc pair he
  · intro h
    refine ⟨(show M.mem (k.eval ρ).val (w.eval ρ).val from hw ▸ h.length), h.function, fun i => ?_, (rows h.length).mpr h.rows,
      fun p c A R e => h.root p.val c.val A.val R.val e.val, h.commute⟩
    exact ⟨fun ⟨p, hp⟩ => (h.domain i.val).mp ⟨p.val, hp⟩, fun hi => by
      obtain ⟨p, hp⟩ := (h.domain i.val).mpr hi
      exact ⟨⟨p, (rd_entry_transitive_l source.transitive (P.eval ρ).property hp).2⟩, hp⟩⟩

theorem Ep_source_d.ja_cell_l {ω κ K Z S : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z S) (nz : Nonempty {x // M.mem x Z})
    {d} (ρ : Env (rt_model_l Z nz) d) (w T Q G E Y W z π s : Term d) (hw : (w.eval ρ).val = ω) :
    Formula.satisfies ρ (ja_cell_m w T Q G E Y W z π s) ↔
      Ja_cell_d I ω (T.eval ρ).val (Q.eval ρ).val (G.eval ρ).val (E.eval ρ).val
        (Y.eval ρ).val (W.eval ρ).val (z.eval ρ).val (π.eval ρ).val (s.eval ρ).val := by
  have pair {a} (η : Env (rt_model_l Z nz) a) (p x y : Term a) : Formula.satisfies η (kpair0_m p x y) ↔
      KPair_d M (p.eval η).val (x.eval η).val (y.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z nz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive nz (kpair0_delta_l p x y) η).trans (kpair0_sat_l hZF.1 ..)
  simp only [ja_cell_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    pair, source.ja_node_l hZF nz, Definitional.Term.eval_weaken, hw]
  exact ⟨fun ⟨k, P, hp, node⟩ => ⟨k.val, P.val, hp, node⟩, fun ⟨k, P, hp, node⟩ =>
    let owned := hp.mem_l M source.transitive (s.eval ρ).property
    ⟨⟨k, owned.1⟩, ⟨P, owned.2⟩, hp, node⟩⟩

/-- 扩展关系只读取已有节点的坐标，故仅需传递性。 -/
theorem ja_extend_relative_l (hE : Extensional M) {Z : M.Domain} (hZ : M.TransitiveSet Z)
    (nz : Nonempty {x // M.mem x Z}) {d} (ρ : Env (rt_model_l Z nz) d) (T s t : Term d) :
    Formula.satisfies ρ (ja_extend_m T s t) ↔ Ja_extend_d (T.eval ρ).val (s.eval ρ).val (t.eval ρ).val := by
  have pair {a} (η : Env (rt_model_l Z nz) a) (p x y : Term a) : Formula.satisfies η (kpair0_m p x y) ↔
      KPair_d M (p.eval η).val (x.eval η).val (y.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z nz) (N := M) Subtype.val] using
      (rt_model_delta_l hZ nz (kpair0_delta_l p x y) η).trans (kpair0_sat_l hE ..)
  have entry {a} (η : Env (rt_model_l Z nz) a) (x y f : Term a) : Formula.satisfies η (rd_entry0_m x y f) ↔
      Rd_entry_d (x.eval η).val (y.eval η).val (f.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z nz) (N := M) Subtype.val] using
      (rt_model_delta_l hZ nz (rd_entry0_delta_l x y f) η).trans (rd_entry0_sat_l hE ..)
  have sub {a} (η : Env (rt_model_l Z nz) a) (x y : Term a) : Formula.satisfies η (Formula.subset x y) ↔
      M.MemberSubset (x.eval η).val (y.eval η).val := by
    simpa only [Formula.subset, Structure.MemberSubset, eval_image_env_l (M := rt_model_l Z nz) (N := M) Subtype.val] using
      (rt_model_delta_l hZ nz (.atom ..) η).trans (Formula.satisfies_subset_iff _ x y)
  simp only [ja_extend_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, pair,
    Formula.satisfies_mem_iff, entry, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, sub,
    Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨k, P, l, Q, hp, hq, hk, ht, subs⟩
    refine ⟨k.val, P.val, l.val, Q.val, hp, hq, hk, ht, fun i p q hip hiq => ?_⟩
    have ip := rd_entry_transitive_l hZ P.property hip
    have iq := rd_entry_transitive_l hZ Q.property hiq
    exact subs ⟨i, ip.1⟩ ⟨p, ip.2⟩ ⟨q, iq.2⟩ hip hiq
  · rintro ⟨k, P, l, Q, hp, hq, hk, ht, subs⟩
    have kp := hp.mem_l M hZ (s.eval ρ).property
    have lq := hq.mem_l M hZ (t.eval ρ).property
    exact ⟨⟨k, kp.1⟩, ⟨P, kp.2⟩, ⟨l, lq.1⟩, ⟨Q, lq.2⟩, hp, hq, hk, ht,
      fun i p q => subs i.val p.val q.val⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一联合尝试树沿实际初等图搬运

参数依次为 ω、T、Q、G、枚举、目标、隶属关系、根、指定图、节点集及扩展关系。
像中的节点与严格扩展由原公式读取，输出明确量化目标实际拥有的节点。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ja_space_d.image_l {ω κ K X R μ K' Y S c d j : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (ρ η : Env M 11) (hw : ρ.bound 0 = ω) (images : ∀ i, Rd_entry_d (ρ.bound i) (η.bound i) j)
    (space : Ja_space_d I ω (ρ.bound 1) (ρ.bound 2) (ρ.bound 3) (ρ.bound 4)
      (ρ.bound 5) (ρ.bound 6) (ρ.bound 7) (ρ.bound 8) (ρ.bound 9) (ρ.bound 10)) :
    (∀ s, M.mem s Y → (M.mem s (η.bound 9) ↔ Ja_cell_d I ω (η.bound 1) (η.bound 2)
      (η.bound 3) (η.bound 4) (η.bound 5) (η.bound 6) (η.bound 7) (η.bound 8) s)) ∧
    (∀ s t, M.mem s Y → M.mem t Y → (Rd_entry_d t s (η.bound 10) ↔
      M.mem s (η.bound 9) ∧ M.mem t (η.bound 9) ∧ Ja_extend_d (η.bound 1) s t)) := by
  let x : Nonempty {a // M.mem a X} := ⟨⟨ω, source.omega_mem⟩⟩
  let y : Nonempty {a // M.mem a Y} := ⟨⟨ω, target.omega_mem⟩⟩
  let ρ' : Env (rt_model_l X x) 11 :=
    ⟨fun i => ⟨ρ.bound i, hj.1.1.input_mem_of_pairMember (images i)⟩, fun _ => ⟨ω, source.omega_mem⟩⟩
  let η' : Env (rt_model_l Y y) 11 :=
    ⟨fun i => ⟨η.bound i, hj.1.1.output_mem_of_pairMember (images i)⟩, fun _ => ⟨ω, target.omega_mem⟩⟩
  have fixed := hj.omega_l I hZF source.omega source.transitive target.transitive hm hn source.omega_mem
  have hw' := hj.1.1.1.2 ω (η.bound 0) ω (hw ▸ images 0) fixed
  let a (i : Fin 11) : Term 11 := .bound i
  let φ : Formula 1 11 := set[11] ⟪
    (∀ s, s ∈ ⌜a 9⌝ₛ ↔ ⌜ja_cell_m⌝ₚ(⌜a 0⌝ₛ, ⌜a 1⌝ₛ, ⌜a 2⌝ₛ, ⌜a 3⌝ₛ,
      ⌜a 4⌝ₛ, ⌜a 5⌝ₛ, ⌜a 6⌝ₛ, ⌜a 7⌝ₛ, ⌜a 8⌝ₛ, s)) ∧
    (∀ s t, ⌜rd_entry0_m⌝ₚ(t, s, ⌜a 10⌝ₛ) ↔
      s ∈ ⌜a 9⌝ₛ ∧ t ∈ ⌜a 9⌝ₛ ∧ ⌜ja_extend_m⌝ₚ(⌜a 1⌝ₛ, s, t))⟫
  have read {κ K Z R} (src : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z R) (nz : Nonempty {s // M.mem s Z})
      (θ : Env (rt_model_l Z nz) 11) (hw : (θ.bound 0).val = ω) : Formula.satisfies θ φ ↔
      (∀ s : (rt_model_l Z nz).Domain, M.mem s.val (θ.bound 9).val ↔ Ja_cell_d I ω
        (θ.bound 1).val (θ.bound 2).val (θ.bound 3).val (θ.bound 4).val (θ.bound 5).val
        (θ.bound 6).val (θ.bound 7).val (θ.bound 8).val s.val) ∧
      (∀ s t : (rt_model_l Z nz).Domain, Rd_entry_d t.val s.val (θ.bound 10).val ↔
        M.mem s.val (θ.bound 9).val ∧ M.mem t.val (θ.bound 9).val ∧ Ja_extend_d (θ.bound 1).val s.val t.val) := by
    have entry {b} (ζ : Env (rt_model_l Z nz) b) (s t f : Term b) : Formula.satisfies ζ (rd_entry0_m s t f) ↔
        Rd_entry_d (s.eval ζ).val (t.eval ζ).val (f.eval ζ).val := by
      simpa only [eval_image_env_l (M := rt_model_l Z nz) (N := M) Subtype.val] using
        (rt_model_delta_l src.transitive nz (rd_entry0_delta_l s t f) ζ).trans (rd_entry0_sat_l hZF.1 ..)
    simp only [φ, a, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
      Formula.satisfies_mem_iff, src.ja_cell_l hZF nz, ja_extend_relative_l hZF.1 src.transitive nz,
      entry, Definitional.Term.eval_weaken, Term.eval_bound, hw]
    rfl
  obtain ⟨o, ho⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l I hZF source.omega ⟨c, R, d, S, hm.empty_pred_l I ho, hn.empty_pred_l I ho, hj⟩
    x y φ (by simp -implicitDefEqProofs [φ, a, Definitional.Formula.FreeClosed]) ρ' η' images
  obtain ⟨nodes, edges⟩ := (read target y η' hw').mp
    (tr.mp ((read source x ρ' hw).mpr ⟨fun s => space.nodes s.val, fun s t => space.edges s.val t.val⟩))
  exact ⟨fun s hs => nodes ⟨s, hs⟩, fun s t hs ht => edges ⟨s, hs⟩ ⟨t, ht⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 联合有限尝试的实际拥有性

每行是内部有限列；前驱定义域是有限序数内的源内分离集。原行图由有限
部分图闭性回收，因此像中的节点判定可用于背景实际构造的全部联合尝试。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ja_node_d.member_l {ω κ K Z S T Q G E Y W z π k P : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z S) (hT : M.mem T Z) (hY : M.MemberSubset Y Z)
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G) (en : Ja_enum_d I ω ω Q E)
    (node : Ja_node_d I ω T Q G E Y W z π k P) : M.mem P Z := by
  have hk := source.transitive ω source.omega_mem k node.length
  obtain ⟨m, hs, hm⟩ := source.omega.1.2 k node.length
  let ρ : Env M 2 := ⟨Fin.cases k (fun _ => T), fun _ => k⟩
  let φ : UnarySchema 2 := { body := rd_entry0_m .newest (.bound 1) (.bound 2) }
  obtain ⟨c, code⟩ := source.code
  obtain ⟨D, hD, ds⟩ := sc_separate_source_l I hZF source.omega source.transitive code source.theory
    φ (rd_entry0_delta_l ..) ρ (Fin.cases hk (fun _ => hT)) (source.transitive ω source.omega_mem m hm)
  have dom i : M.mem i D ↔ Rd_entry_d i k T := by
    have spec : M.mem i D ↔ M.mem i m ∧ Rd_entry_d i k T :=
      (ds i).trans (and_congr_right fun _ => rd_entry0_sat_l hZF.1 ..)
    exact spec.trans ⟨And.right, fun hi => ⟨(hs i).mpr ((diagram.order.forward i k hi).elim
      (fun e => Or.inr (e ▸ fun _ => Iff.rfl)) Or.inl), hi⟩⟩
  have fn : M.IsSetFunctionFromTo I P D Z := ⟨node.function,
    fun i => (dom i).trans (node.domain i).symm, fun i hi => by
      obtain ⟨p, hp⟩ := (node.domain i).mpr ((dom i).mp hi)
      obtain ⟨a, A, R, ha, ma⟩ := diagram.model_l hZF (diagram.order.bound i k ((dom i).mp hi)).1
      obtain ⟨e, he⟩ := (en.domain i).mp (diagram.order.bound i k ((dom i).mp hi)).1
      exact ⟨p, sc_finite_function_l (ZF.modelsKP hZF) source.omega source.transitive (source.algebra_l (ZF.modelsKP hZF)).pair (source.algebra_l (ZF.modelsKP hZF)).union source.omega_mem
        hY node.length (node.rows i p a A R e hp ha ma.1 he).1, hp⟩⟩
  exact sc_finite_partial_l hZF source.omega source.transitive code source.theory source.omega_mem hD hm
    (fun i hi => ((ds i).mp hi).1) (fn0_of_function_l (ZF.modelsKP hZF) fn)

theorem Ja_cell_d.member_l {ω κ K Z S T Q G E Y W z π s : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K Z S) (hT : M.mem T Z) (hY : M.MemberSubset Y Z)
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω T Q G) (en : Ja_enum_d I ω ω Q E)
    (cell : Ja_cell_d I ω T Q G E Y W z π s) : M.mem s Z := by
  obtain ⟨k, P, pair, node⟩ := cell
  obtain ⟨t, ht, hp⟩ := source.kpair_l hZF (source.transitive ω source.omega_mem k node.length)
    (node.member_l hZF source hT hY diagram en)
  exact kpair_unique_l M hZF.1 hp pair ▸ ht

/-- 像参数仍给出同一类枚举树时，像集合就是全部背景联合节点及其原扩展关系。 -/
theorem Ja_space_d.full_image_l {ω κ K X R μ K' Y S c d j : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (target : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω μ K' Y S)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (ρ η : Env M 11) (hw : ρ.bound 0 = ω) (images : ∀ i, Rd_entry_d (ρ.bound i) (η.bound i) j)
    (space : Ja_space_d I ω (ρ.bound 1) (ρ.bound 2) (ρ.bound 3) (ρ.bound 4)
      (ρ.bound 5) (ρ.bound 6) (ρ.bound 7) (ρ.bound 8) (ρ.bound 9) (ρ.bound 10))
    (diagram : It_diagram_d (kp_pair_l (ZF.modelsKP hZF)) ω ω (η.bound 1) (η.bound 2) (η.bound 3))
    (en : Ja_enum_d I ω ω (η.bound 2) (η.bound 4)) :
    Ja_space_d I ω (η.bound 1) (η.bound 2) (η.bound 3) (η.bound 4)
      (η.bound 5) (η.bound 6) (η.bound 7) (η.bound 8) (η.bound 9) (η.bound 10) := by
  obtain ⟨nodes, edges⟩ := space.image_l hZF source target hm hn hj ρ η hw images
  have owned i := hj.1.1.output_mem_of_pairMember (images i)
  have nodes s : M.mem s (η.bound 9) ↔ Ja_cell_d I ω (η.bound 1) (η.bound 2) (η.bound 3)
      (η.bound 4) (η.bound 5) (η.bound 6) (η.bound 7) (η.bound 8) s :=
    ⟨fun hs => (nodes s (target.transitive _ (owned 9) s hs)).mp hs,
      fun hs => (nodes s (hs.member_l hZF target (owned 1) (target.transitive _ (owned 5)) diagram en)).mpr hs⟩
  let φ : Formula 1 2 := Formula.forallMem (.bound 1) (Formula.existsMem (.bound 1)
    (Formula.existsMem (.bound 2) (kpair0_m (.bound 2) .newest (.bound 1))))
  have read (θ : Env M 2) : Formula.satisfies θ φ ↔ ∀ p, M.mem p (θ.bound 1) →
      ∃ s, M.mem s (θ.bound 0) ∧ ∃ t, M.mem t (θ.bound 0) ∧ KPair_d M p t s := by
    simp only [φ, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff, kpair0_sat_l hZF.1]; rfl
  let a (θ : Env M 11) : Env M 2 := ⟨Fin.cases (θ.bound 9) (fun _ => θ.bound 10), fun _ => ω⟩
  have tr := smap_delta_l I hZF source.omega source.transitive target.transitive hm hn hj φ
    (by simp -implicitDefEqProofs [φ])
    (.forallMem _ (.existsMem _ (.existsMem _ (kpair0_delta_l ..)))) (a ρ) (a η)
    (Fin.cases (images 9) (fun _ => images 10))
  have pairs := (read (a η)).mp (tr.mp ((read (a ρ)).mpr (fun p hp => by
    obtain ⟨t, s, pair⟩ := space.relation p hp
    have edge := (space.edges s t).mp ⟨p, pair, hp⟩
    exact ⟨s, edge.1, t, edge.2.1, pair⟩)))
  refine ⟨nodes, fun p hp => ?_, fun s t => ⟨?_, ?_⟩⟩
  · obtain ⟨s, _, t, _, pair⟩ := pairs p hp
    exact ⟨t, s, pair⟩
  · intro h
    have ts := rd_entry_transitive_l target.transitive (owned 10) h
    exact (edges s t ts.2 ts.1).mp h
  · intro h
    exact (edges s t (target.transitive _ (owned 9) s h.1) (target.transitive _ (owned 9) t h.2.1)).mpr h

end YesMetaZFC.SetTheory.LargeCardinal
