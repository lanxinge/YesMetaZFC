import YesMetaZFC.SetTheory.InnerModel.ProofCode.Initial.Correctness

/-! # Σ₁ 函数在集合上的完整求值表

对已证明在源集合上全且单值的实际 Σ₁ 程序，将输出标上输入，再取集合像。
后续的码名求值表直接实例化此构造。
-/

namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}}

def sg_tag_s {n} (φ : S1_binary n) : S1_binary n where
  matrix := {
    body := Formula.existsMem .newest (Formula.existsMem (.bound 1)
      (.conj (kpair0_m (.bound 3) (.bound 4) (.bound 1))
        (φ.matrix_m (fun i => .bound ⟨i.val + 5, by omega⟩) (.bound 4) (.bound 1) .newest)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed]
    delta0 := .existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (φ.matrix.delta0.bind_l _))) }

theorem sg_tag_sat_l (hKP : M.Models KP) {n} (φ : S1_binary n) (ρ : Env M n) (x p : M.Domain) :
    (sg_tag_s φ).schema.denote ρ x p ↔ ∃ y, φ.schema.denote ρ x y ∧ KPair_d M p x y := by
  rw [S1_binary.sat_l]
  simp only [sg_tag_s, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, kpair0_sat_l hKP.1, S1_binary.matrix_sat_l]
  change (∃ T y, M.mem y T ∧ ∃ W, M.mem W T ∧ KPair_d M p x y ∧ φ.matrix_binary.toBinarySchema.denote (ρ.push x) y W) ↔ _
  refine ⟨fun ⟨_, y, _, W, _, hp, h⟩ => ⟨y, (φ.sat_l ρ x y).mpr ⟨W, h⟩, hp⟩, ?_⟩
  rintro ⟨y, hy, hp⟩
  obtain ⟨W, hw⟩ := (φ.sat_l ρ x y).mp hy
  obtain ⟨T, ht⟩ := KP.exists_pair hKP y W
  exact ⟨T, y, (ht y).mpr (Or.inl rfl), W, (ht W).mpr (Or.inr rfl), hp, hw⟩

def Sg_table_d {n} (φ : S1_binary n) (ρ : Env M n) (X F : M.Domain) : Prop :=
  ∀ p, M.mem p F ↔ ∃ x, M.mem x X ∧ ∃ y, φ.schema.denote ρ x y ∧ KPair_d M p x y
def sg_table_s {n} (φ : S1_binary n) : S1_binary n := (sg_tag_s φ).image

private theorem tag_total_l (hKP : M.Models KP) {n} (φ : S1_binary n) (ρ : Env M n) {X : M.Domain}
    (ht : ∀ x, M.mem x X → ∃ y, φ.schema.denote ρ x y) (x : M.Domain) (hx : M.mem x X) :
    ∃ p, (sg_tag_s φ).schema.denote ρ x p := by
  obtain ⟨y, hy⟩ := ht x hx
  obtain ⟨p, hp⟩ := (kp_pair_l hKP).total x y
  exact ⟨p, (sg_tag_sat_l hKP φ ρ x p).mpr ⟨y, hy, hp⟩⟩

private theorem tag_unique_l (hKP : M.Models KP) {n} (φ : S1_binary n) (ρ : Env M n) {X : M.Domain}
    (hu : ∀ x, M.mem x X → ∀ y z, φ.schema.denote ρ x y → φ.schema.denote ρ x z → y = z)
    (x : M.Domain) (hx : M.mem x X) (p q : M.Domain)
    (hp : (sg_tag_s φ).schema.denote ρ x p) (hq : (sg_tag_s φ).schema.denote ρ x q) : p = q := by
  obtain ⟨y, hy, hp⟩ := (sg_tag_sat_l hKP φ ρ x p).mp hp
  obtain ⟨z, hz, hq⟩ := (sg_tag_sat_l hKP φ ρ x q).mp hq
  have he := hu x hx y z hy hz; subst z
  exact kpair_unique_l M hKP.1 hp hq

theorem sg_table_sat_l (hKP : M.Models KP) {n} (φ : S1_binary n) (ρ : Env M n) (X F : M.Domain)
    (ht : ∀ x, M.mem x X → ∃ y, φ.schema.denote ρ x y)
    (hu : ∀ x, M.mem x X → ∀ y z, φ.schema.denote ρ x y → φ.schema.denote ρ x z → y = z) :
    (sg_table_s φ).schema.denote ρ X F ↔ Sg_table_d φ ρ X F := by
  rw [sg_table_s, S1_binary.image_sat_l hKP _ _ _ _ (tag_total_l hKP φ ρ ht) (tag_unique_l hKP φ ρ hu)]
  simp only [sg_tag_sat_l hKP, Sg_table_d]

theorem sg_table_exists_l (hKP : M.Models KP) {n} (φ : S1_binary n) (ρ : Env M n) (X : M.Domain)
    (ht : ∀ x, M.mem x X → ∃ y, φ.schema.denote ρ x y)
    (hu : ∀ x, M.mem x X → ∀ y z, φ.schema.denote ρ x y → φ.schema.denote ρ x z → y = z) :
    ∃ F, Sg_table_d φ ρ X F := by
  obtain ⟨F, hf⟩ := KP.s1_image_l hKP (sg_tag_s φ) ρ X (tag_total_l hKP φ ρ ht) (tag_unique_l hKP φ ρ hu)
  exact ⟨F, fun p => (hf p).trans (exists_congr fun x => and_congr_right fun _ => sg_tag_sat_l hKP φ ρ x p)⟩

theorem Sg_table_d.entry_l (hKP : M.Models KP) {n} {φ : S1_binary n} {ρ : Env M n} {X F x y : M.Domain}
    (hf : Sg_table_d φ ρ X F) : Rd_entry_d x y F ↔ M.mem x X ∧ φ.schema.denote ρ x y := by
  constructor
  · rintro ⟨p, hp, hpF⟩
    obtain ⟨a, ha, b, hb, h⟩ := (hf p).mp hpF
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M h hp
    exact ⟨ha, hb⟩
  · rintro ⟨hx, hy⟩
    obtain ⟨p, hp⟩ := (kp_pair_l hKP).total x y
    exact ⟨p, hp, (hf p).mpr ⟨x, hx, y, hy, hp⟩⟩

theorem pn_eval_domain_l {v x : M.Domain} (hx : Pn_eval_d v x) : Pn_valid_d v :=
  hx.elim fun a ha => ha.elim fun h hh => hh.elim fun c hc => ⟨a, h, c, hc.1⟩

theorem pn_eval_table_exists_l (hM : M.Models KPi) {X : M.Domain} (hx : ∀ v, M.mem v X → Pn_valid_d v) (ρ : Env M 0) :
    ∃ F, Sg_table_d pn_eval_s ρ X F :=
  sg_table_exists_l (KPi.models_iff_l.mp hM).1 pn_eval_s ρ X
    (fun v hv => (pn_eval_total_l hM (hx v hv)).imp (fun x h => (pn_eval_sat_l (KPi.models_iff_l.mp hM).1 ρ v x).mpr h))
    (fun v _ x y hx hy => pn_eval_unique_l hM ((pn_eval_sat_l (KPi.models_iff_l.mp hM).1 ρ v x).mp hx)
      ((pn_eval_sat_l (KPi.models_iff_l.mp hM).1 ρ v y).mp hy))

theorem pn_eval_table_sat_l (hM : M.Models KPi) {X F : M.Domain} (hx : ∀ v, M.mem v X → Pn_valid_d v) (ρ : Env M 0) :
    (sg_table_s pn_eval_s).schema.denote ρ X F ↔ Sg_table_d pn_eval_s ρ X F :=
  sg_table_sat_l (KPi.models_iff_l.mp hM).1 pn_eval_s ρ X F
    (fun v hv => (pn_eval_total_l hM (hx v hv)).imp (fun x h => (pn_eval_sat_l (KPi.models_iff_l.mp hM).1 ρ v x).mpr h))
    (fun v _ x y hx hy => pn_eval_unique_l hM ((pn_eval_sat_l (KPi.models_iff_l.mp hM).1 ρ v x).mp hx)
      ((pn_eval_sat_l (KPi.models_iff_l.mp hM).1 ρ v y).mp hy))

end YesMetaZFC.SetTheory.InnerModel
