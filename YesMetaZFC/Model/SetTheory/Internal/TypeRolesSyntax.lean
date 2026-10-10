import YesMetaZFC.Model.SetTheory.Internal.Syntax
import YesMetaZFC.SetTheory.KP.Kuratowski
import YesMetaZFC.SetTheory.KP.Natural
import YesMetaZFC.SetTheory.Notation

/-! # 类型坐标的固定标签角色

第 i+1 个坐标必须是以内部自然数 i 为首坐标的 Kuratowski 对。
零标签与相邻标签的后继关系都是有界公式，因而在传递秩层间绝对。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}}

def Tr_tag_d (i p : M.Domain) : Prop := ∃ x, KPair_d M p i x

def tr_tag_m {d} (i p : Term d) : Formula 1 d := set[d] ⟪
  ∃ a ∈ ⌜p⌝ₛ, ∃ x ∈ a, ⌜kpair0_m⌝ₚ(⌜p⌝ₛ, ⌜i⌝ₛ, x)⟫
derive_free_closed tr_tag_m

theorem tr_tag_delta_l {d} (i p : Term d) : (tr_tag_m i p).IsDelta0 :=
  .existsMem _ (.existsMem _ (kpair0_delta_l ..))

theorem tr_tag_sat_l (hE : Extensional M) {d} (ρ : Env M d) (i p : Term d) :
    Formula.satisfies ρ (tr_tag_m i p) ↔ Tr_tag_d (i.eval ρ) (p.eval ρ) := by
  simp only [tr_tag_m, Formula.satisfies_existsMem_iff, kpair0_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨_, _, x, _, h⟩ => ⟨x, h⟩, fun ⟨x, h⟩ => by
    obtain ⟨a, ha, hx⟩ := (kpair_union_l M h x).mpr (Or.inr rfl)
    exact ⟨a, ha, x, hx, h⟩⟩

theorem Tr_tag_d.unique_l {i j p : M.Domain} (h : Tr_tag_d i p) (g : Tr_tag_d j p) : i = j := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨y, hy⟩ := g
  exact (kpair_injective_l M hx hy).1

def Tr_zero_d (p : M.Domain) : Prop := ∃ i, (∀ x, ¬ M.mem x i) ∧ Tr_tag_d i p
def Tr_step_d (p q : M.Domain) : Prop := ∃ i j, Tr_tag_d i p ∧ Tr_tag_d j q ∧ M.SuccessorOf j i

def tr_zero_m {d} (p : Term d) : Formula 1 d := set[d] ⟪
  ∃ a ∈ ⌜p⌝ₛ, ∃ i ∈ a, (∀ x ∈ i, ⊥) ∧ ⌜tr_tag_m⌝ₚ(i, ⌜p⌝ₛ)⟫
derive_free_closed tr_zero_m

def tr_step_m {d} (p q : Term d) : Formula 1 d := set[d] ⟪
  ∃ a ∈ ⌜p⌝ₛ, ∃ i ∈ a, ∃ b ∈ ⌜q⌝ₛ, ∃ j ∈ b,
    ⌜tr_tag_m⌝ₚ(i, ⌜p⌝ₛ) ∧ ⌜tr_tag_m⌝ₚ(j, ⌜q⌝ₛ) ∧ ⌜KP.succ0_m⌝ₚ(j, i)⟫
derive_free_closed tr_step_m

theorem tr_zero_delta_l {d} (p : Term d) : (tr_zero_m p).IsDelta0 :=
  .existsMem _ (.existsMem _ (.conj (.forallMem _ .falsum) (tr_tag_delta_l ..)))

theorem tr_step_delta_l {d} (p q : Term d) : (tr_step_m p q).IsDelta0 :=
  .existsMem _ (.existsMem _ (.existsMem _ (.existsMem _
    (.conj (tr_tag_delta_l ..) (.conj (tr_tag_delta_l ..) (KP.succ0_delta_l ..))))))

theorem tr_zero_sat_l (hE : Extensional M) {d} (ρ : Env M d) (p : Term d) :
    Formula.satisfies ρ (tr_zero_m p) ↔ Tr_zero_d (p.eval ρ) := by
  simp only [tr_zero_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_forallMem_iff, Formula.satisfies_falsum_iff, tr_tag_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨_, _, i, _, hi, hp⟩ => ⟨i, hi, hp⟩, fun ⟨i, hi, x, hp⟩ => by
    obtain ⟨a, ha, hx⟩ := (kpair_union_l M hp i).mpr (Or.inl rfl)
    exact ⟨a, ha, i, hx, hi, x, hp⟩⟩

theorem tr_step_sat_l (hE : Extensional M) {d} (ρ : Env M d) (p q : Term d) :
    Formula.satisfies ρ (tr_step_m p q) ↔ Tr_step_d (p.eval ρ) (q.eval ρ) := by
  simp only [tr_step_m, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
    tr_tag_sat_l hE, KP.succ0_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun ⟨_, _, i, _, _, _, j, _, hp, hq, hs⟩ => ⟨i, j, hp, hq, hs⟩,
    fun ⟨i, j, ⟨x, hp⟩, ⟨y, hq⟩, hs⟩ => by
      obtain ⟨a, ha, hi⟩ := (kpair_union_l M hp i).mpr (Or.inl rfl)
      obtain ⟨b, hb, hj⟩ := (kpair_union_l M hq j).mpr (Or.inl rfl)
      exact ⟨a, ha, i, hi, b, hb, j, hj, ⟨x, hp⟩, ⟨y, hq⟩, hs⟩⟩

theorem tr_zero_iff_l (hE : Extensional M) {e p} (he : ∀ x, ¬ M.mem x e) :
    Tr_zero_d p ↔ Tr_tag_d e p := by
  refine ⟨fun ⟨i, hi, hp⟩ => ?_, fun h => ⟨e, he, h⟩⟩
  exact hE.eq_of_same_members i e (fun x => iff_of_false (hi x) (he x)) ▸ hp

theorem tr_step_iff_l (hE : Extensional M) {i j p q} (hp : Tr_tag_d i p) (hs : M.SuccessorOf j i) :
    Tr_step_d p q ↔ Tr_tag_d j q := by
  refine ⟨fun ⟨a, b, ha, hb, ht⟩ => ?_, fun hq => ⟨i, j, hp, hq, hs⟩⟩
  have eq := ha.unique_l hp; subst a
  exact ht.eq hE hs ▸ hb

variable {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Tr_roles_d (k f : M.Domain) : Prop := ∀ i j p,
  M.mem i k → M.SuccessorOf j i → M.PairMember I j p f → Tr_tag_d i p

def tr_roles_m {d} (k f : Term d) : Formula 1 d := set[d] ⟪∀ i ∈ ⌜k⌝ₛ, ∀ j p,
  ⌜KP.succ0_m⌝ₚ(j, i) → ⌜Formula.orderedPairMem 𝒞⌝ₚ(j, p, ⌜f⌝ₛ) → ⌜tr_tag_m⌝ₚ(i, p)⟫
derive_free_closed tr_roles_m

theorem tr_roles_sat_l (hE : Extensional M) {d} (ρ : Env M d) (k f : Term d) :
    Formula.satisfies ρ (tr_roles_m (𝒞 := 𝒞) k f) ↔ Tr_roles_d I (k.eval ρ) (f.eval ρ) := by
  simp only [tr_roles_m, Tr_roles_d, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, KP.succ0_sat_l hE, Formula.satisfies_orderedPairMem_iff I,
    tr_tag_sat_l hE, Definitional.Term.eval_weaken]
  exact ⟨fun h i j p hi => h i hi j p, fun h i hi j p => h i j p hi⟩

theorem tr_roles_last_l (hE : Extensional M) {k l f q} (hs : M.SuccessorOf l k)
    (hf : M.IsSetFunction I f) (hq : M.PairMember I l q f) :
    Tr_roles_d I l f ↔ Tr_roles_d I k f ∧ Tr_tag_d k q := by
  constructor
  · intro h
    exact ⟨fun i j p hi => h i j p ((hs i).mpr (Or.inl hi)), h k l q hs.predecessor_mem hs hq⟩
  · rintro ⟨h, tag⟩ i j p hi hj hp
    rcases (hs i).mp hi with hi | hi
    · exact h i j p hi hj hp
    · have eq := hE.eq_of_same_members i k hi; subst i
      have eq := hj.eq hE hs; subst j
      exact (hf.2 l q p hq hp) ▸ tag

end YesMetaZFC.SetTheory.Internal
