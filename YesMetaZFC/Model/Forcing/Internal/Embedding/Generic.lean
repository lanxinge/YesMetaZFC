import YesMetaZFC.Model.Forcing.Internal.Embedding.Lift

/-! # 旧小偏序的泛型性向初等目标传递

把目标稠密集先与条件域相交，再取其实际旧原像。所有目标条件都有旧来源，
所以稠密性反射回源模型，源泛型性即可遇到目标稠密集。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
open SetTheory.Definitional.Project.FirstOrderSemantics
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}
section Relations
variable (hM : Extensional M) (hN : Extensional N)
  (j : M.Domain → N.Domain) (hj : Pe_d j)
local notation "e" => j
include hM hN hj

omit hM hN in
theorem em_member_l (a b : M.Domain) : M.mem a b ↔ N.mem (e a) (e b) := by
  let ρ : Env M 2 := ⟨Fin.cases b (fun _ => a), fun _ => a⟩
  let φ : Formula 1 2 := .mem (.bound 1) .newest
  have hc : φ.FreeClosed := by simp -implicitDefEqProofs [φ, Definitional.Formula.FreeClosed]
  exact hj φ hc ρ

theorem em_entry_l (a b R : M.Domain) : Entry_d M a b R ↔ Entry_d N (e a) (e b) (e R) := by
  let ρ : Env M 3 := ⟨Fin.cases R (Fin.cases b (fun _ => a)), fun _ => a⟩
  exact (entry_sat_l M hM ρ (.bound 2) (.bound 1) .newest).symm.trans
    ((hj (entry_m (.bound 2) (.bound 1) .newest)
      (by simp -implicitDefEqProofs) ρ).trans (entry_sat_l N hN (image_env_l e ρ) (.bound 2) (.bound 1) .newest))

theorem em_below_l (P R z q p : M.Domain) :
    Below_d M P R z q p ↔ Below_d N (e P) (e R) (e z) (e q) (e p) :=
  and_congr (em_member_l j hj q P) (and_congr
    (not_congr ⟨congrArg e, fun h => hj.injective_l hM hN h⟩) (em_entry_l hM hN j hj q p R))

end Relations

def Em_generic_d {M : Structure.{u}} {N : Structure.{v}}
    (f : M.Domain → N.Domain) (U : M.Domain → Prop) (q : N.Domain) : Prop :=
  ∃ p, U p ∧ f p = q

section Generic
variable (hM : Extensional M) (hN : N.Models KP) (j : M.Domain → N.Domain) (hj : Pe_d j)
local notation "e" => j
include hM hN hj

theorem em_generic_l {P R z : M.Domain} {U : M.Domain → Prop}
    (hU : Generic_d M P R z U)
    (conditions : ∀ q, N.mem q (e P) → ∃ p, M.mem p P ∧ e p = q)
    (subsets : ∀ D, N.MemberSubset D (e P) → ∃ C, e C = D) :
    Generic_d N (e P) (e R) (e z) (Em_generic_d e U) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro q ⟨p, hp, rfl⟩
    exact ⟨(em_member_l j hj p P).mp (hU.proper p hp).1,
      fun eq => (hU.proper p hp).2 (hj.injective_l hM hN.1 eq)⟩
  · obtain ⟨p, hp⟩ := hU.inhabited
    exact ⟨e p, p, hp, rfl⟩
  · rintro p q ⟨a, ha, rfl⟩ hq pq
    obtain ⟨b, hb, rfl⟩ := conditions q hq
    exact ⟨b, hU.upward a b ha hb ((em_entry_l hM hN.1 j hj a b R).mpr pq), rfl⟩
  · rintro p q ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    obtain ⟨c, hc, ca, cb⟩ := hU.directed a b ha hb
    exact ⟨e c, ⟨c, hc, rfl⟩, (em_entry_l hM hN.1 j hj c a R).mp ca, (em_entry_l hM hN.1 j hj c b R).mp cb⟩
  · rintro p ⟨a, ha, rfl⟩ D dense
    obtain ⟨K, inter⟩ := KP.intersection_exists_d hN D (e P)
    obtain ⟨C, eq⟩ := subsets K (fun q hq => ((inter q).mp hq).2)
    have dense' : Dense_d M P R z (fun q => M.mem q C) a := by
      intro b hb
      obtain ⟨q, hq, hd⟩ := dense (e b) ((em_below_l hM hN.1 j hj P R z b a).mp hb)
      obtain ⟨c, _, rfl⟩ := conditions q hq.1
      exact ⟨c, (em_below_l hM hN.1 j hj P R z c b).mpr hq,
        (em_member_l j hj c C).mpr (eq.symm ▸ (inter (e c)).mpr ⟨hd, hq.1⟩)⟩
    obtain ⟨q, hq, qc⟩ := hU.meets a ha C dense'
    exact ⟨e q, ⟨q, hq, rfl⟩, ((inter (e q)).mp (eq ▸ (em_member_l j hj q C).mp qc)).1⟩

end Generic

variable (hM : M.Models ZF) (hN : N.Models ZF) (j : M.Domain → N.Domain) (hj : Pe_d j)
local notation "e" => j
include hj

/-- 完整条件像及子集像已经足够，目标泛型性在此实际证明。 -/
theorem em_small_lift_l {P R z : M.Domain} {U : M.Domain → Prop}
    (O : Cond_order_d M P R z) (hU : Generic_d M P R z U)
    (conditions : ∀ q, N.mem q (e P) → ∃ p, M.mem p P ∧ e p = q)
    (subsets : ∀ D, N.MemberSubset D (e P) → ∃ C, e C = D) :
    let V := Em_generic_d e U
    Generic_d N (e P) (e R) (e z) V ∧
    ∃ f : (extension_l M hM P R z U).Domain → (extension_l N hN (e P) (e R) (e z) V).Domain,
      Function.Injective f ∧
      (∀ t x, Qval_d M P R z U t x → Qval_d N (e P) (e R) (e z) V (e t) (f x)) ∧
      ∀ {n} (φ : Formula 1 n), φ.FreeClosed → ∀ ρ, Formula.satisfies ρ φ ↔ Formula.satisfies (image_env_l f ρ) φ := by
  have hV := em_generic_l hM.1 (ZF.modelsKP hN) j hj hU conditions subsets
  have accepted p (hp : U p) : Em_generic_d e U (e p) := ⟨p, hp, rfl⟩
  exact ⟨hV, em_lift_l hM.1 hN.1 j hj accepted, em_lift_injective_l hM hN j hj accepted O hU hV,
    fun _ _ => em_lift_value_l hM.1 hN.1 j hj accepted, em_lift_elementary_l hM hN j hj accepted O hU hV⟩

end YesMetaZFC.Model.Forcing.Internal
