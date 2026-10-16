import YesMetaZFC.Model.Forcing.Internal.Embedding.Transport
import YesMetaZFC.Model.Forcing.Internal.Ground.Transfer

/-! # 初等嵌入的实际泛型商提升

按 [τ]↦[j(τ)] 直接定义商映射。接受原泛型条件的像保证代表元无关；
完整初等性由原力迫真值定理和否定反射给出。构造不选取商代表元。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
open SetTheory.Definitional.Project.FirstOrderSemantics
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}
variable {P R z : M.Domain} {U : M.Domain → Prop} {V : N.Domain → Prop}
section Quotient
variable (hM : Extensional M) (hN : Extensional N)
  (j : M.Domain → N.Domain) (hj : Pe_d j) (accepted : ∀ p, U p → V (j p))
local notation "e" => j
include hM hN hj accepted

def em_lift_l : Name_quot_l M P R z U → Name_quot_l N (e P) (e R) (e z) V :=
  Quot.lift (fun t : {t : M.Domain // Name_d M P t} =>
    Quot.mk (Name_eq_d N (e P) (e R) (e z) V) ⟨e t.1, (em_name_l hM hN j hj).mp t.2⟩) (by
    rintro s t ⟨p, hp, eq⟩
    exact Quot.sound ⟨e p, accepted p hp, (em_eq_force_l hM hN j hj).mp eq⟩)

theorem em_lift_value_l {t x} (value : Qval_d M P R z U t x) :
    Qval_d N (e P) (e R) (e z) V (e t) (em_lift_l hM hN j hj accepted x) := by
  obtain ⟨ht, rfl⟩ := value
  exact ⟨(em_name_l hM hN j hj).mp ht, rfl⟩

end Quotient

variable (hM : M.Models ZF) (hN : N.Models ZF)
  (j : M.Domain → N.Domain) (hj : Pe_d j) (accepted : ∀ p, U p → V (j p))
local notation "e" => j
include hM hN hj accepted
variable (O : Cond_order_d M P R z) (hU : Generic_d M P R z U)
  (hV : Generic_d N (j P) (j R) (j z) V)
local notation "E" => extension_l M hM P R z U
local notation "D" => extension_l N hN (e P) (e R) (e z) V
include O hU hV

theorem em_lift_elementary_l {n} (φ : Formula 1 n) (hc : φ.FreeClosed) (ρ : Env E n) :
    Formula.satisfies ρ φ ↔ Formula.satisfies
      (@image_env_l E D (em_lift_l hM.1 hN.1 j hj accepted (P := P) (R := R) (z := z)) n ρ) φ := by
  let f : (E).Domain → (D).Domain := em_lift_l hM.1 hN.1 j hj accepted
  have target := em_order_l hM.1 hN.1 j hj O
  obtain ⟨η, values⟩ := lift_env_l hM ρ
  have values' : Env_val_d hN (@image_env_l M N e n η) (@image_env_l E D f n ρ) := by
    intro t
    cases t with
    | bound i => exact em_lift_value_l hM.1 hN.1 j hj accepted (values (.bound i))
    | free i => exact em_lift_value_l hM.1 hN.1 j hj accepted (values (.free i))
  have forward (ψ : Formula 1 n) (hs : ψ.FreeClosed) (h : Formula.satisfies ρ ψ) :
      Formula.satisfies (image_env_l f ρ) ψ := by
    obtain ⟨p, hp, forced⟩ := (forcing_truth_l O hM hU ψ hs η ρ values).mpr h
    exact (forcing_truth_l target hN hV ψ hs (image_env_l e η) (image_env_l f ρ) values').mp
      ⟨e p, accepted p hp, (em_forces_l j hj ψ hs η P R z p).mp forced⟩
  refine ⟨forward φ hc, fun h => Classical.byContradiction (fun no => ?_)⟩
  exact forward (.neg φ) hc no h

theorem em_lift_injective_l : Function.Injective (em_lift_l hM.1 hN.1 j hj accepted (P := P) (R := R) (z := z)) := by
  intro x y eq
  let ρ : Env E 2 := ⟨Fin.cases y (fun _ => x), fun _ => x⟩
  have tr := em_lift_elementary_l hM hN j hj accepted O hU hV
    (Formula.extensionalEq (.bound 1) .newest) (by simp -implicitDefEqProofs) ρ
  exact (Formula.satisfies_extensionalEq_iff_eq (extension_ext_l O hM hU) ρ (.bound 1) .newest).mp
    (tr.mpr ((Formula.satisfies_extensionalEq_iff_eq (extension_ext_l (em_order_l hM.1 hN.1 j hj O) hN hV)
      (@image_env_l E D (em_lift_l hM.1 hN.1 j hj accepted (P := P) (R := R) (z := z)) 2 ρ)
        (.bound 1) .newest).mpr eq))

/-- 自动构造两侧规范地嵌入，并验证提升与原嵌入的交换方块。 -/
theorem em_lift_ground_l {p : M.Domain} (hp : U p) :
    ∃ a : M.Domain → (E).Domain, ∃ b : N.Domain → (D).Domain,
      (∀ x t, Check_d M p x t → Qval_d M P R z U t (a x)) ∧
      (∀ y t, Check_d N (e p) y t → Qval_d N (e P) (e R) (e z) V t (b y)) ∧
      ∀ x, em_lift_l hM.1 hN.1 j hj accepted (a x) = b (e x) := by
  obtain ⟨a, ha, _, _⟩ := check_map_l O hM hU hp
  obtain ⟨b, hb, _, _⟩ := check_map_l (em_order_l hM.1 hN.1 j hj O) hN hV (accepted p hp)
  refine ⟨a, b, ha, hb, fun x => ?_⟩
  obtain ⟨t, ht, _⟩ := zf_check_l M hM (hU.proper p hp).1 x
  exact qval_unique_l (em_lift_value_l hM.1 hN.1 j hj accepted (ha x t ht))
    (hb (e x) (e t) ((em_check_l hM.1 hN.1 j hj).mp ht))

end YesMetaZFC.Model.Forcing.Internal
