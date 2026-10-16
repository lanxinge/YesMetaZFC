import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.FormulaImage

/-! # 完整关系 Łoś 在传递像中的有界解码

商计算全部交给一般关系版本；这里仅在源端和目标端使用 Δ₀ 绝对性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rs_delta_image_l {ω a X R D U c G p C T d Y S j : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hm : Smem_d I a X R)
    (theory : Sc_theory_d I ω X R) (uniform : Sc_uniform_d I ω X R D) (hD : M.mem D X) (hU : Sf_ultra_d X D U)
    (hG : ∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D X f) (model : Rp_model_d I D X U R c G p C T)
    (hY : M.TransitiveSet Y) (target : Smem_d I d Y S) (hj : Smap_d I ω c d C Y j)
    {n} (φ : Formula 1 n) (hφ : φ.FreeClosed) (hd : φ.IsDelta0)
    (f : Fin n → M.Domain) (hf : ∀ i, M.mem (f i) G) (ρ : Env M n)
    (values : ∀ i, ∃ B, Rd_entry_d (f i) B p ∧ Rd_entry_d B (ρ.bound i) j) :
    Formula.satisfies ρ φ ↔ ∃ A, M.mem A X ∧ M.mem A U ∧ M.MemberSubset A D ∧
      ∀ v, M.mem v A → ∀ η : Env M n, (∀ i, Rd_entry_d v (η.bound i) (f i)) → Formula.satisfies η φ := by
  obtain ⟨y, hy⟩ := target.1.2.1
  let θ : Env (smdl_structure_l I (R := S) target.1.2.1) n :=
    ⟨fun i => ⟨ρ.bound i, (values i).elim fun _ h => hj.1.1.output_mem_of_pairMember h.2⟩, fun _ => ⟨y, hy⟩⟩
  have read : Formula.satisfies θ φ ↔ Formula.satisfies ρ φ :=
    (smem_delta_image_l I target hY hd θ).trans (Formula.closed_env_l φ hφ rfl)
  have los := rs_formula_image_l hZF hω hX hm theory uniform hD hU hG model target.1 hj φ hφ f hf θ values
  refine read.symm.trans (los.trans ?_)
  apply exists_congr
  intro A
  apply and_congr_right
  intro hAX
  apply and_congr_right
  intro hAU
  apply and_congr_right
  intro hAD
  constructor
  · intro holds s hs η entries
    obtain ⟨x, hx⟩ := hm.1.2.1
    let η' : Env (smdl_structure_l I (R := R) hm.1.2.1) n :=
      ⟨fun i => ⟨η.bound i, ((hG (f i)).mp (hf i)).2.bound_l (entries i) |>.2⟩, fun _ => ⟨x, hx⟩⟩
    exact (Formula.closed_env_l φ hφ (ρ := image_env_l Subtype.val η') (η := η) rfl).mp
      ((smem_delta_image_l I hm hX hd η').mp (holds s hs η' entries))
  · intro holds s hs η entries
    exact (smem_delta_image_l I hm hX hd η).mpr
      (holds s hs ⟨fun i => (η.bound i).val, fun i => (η.free i).val⟩ entries)

end YesMetaZFC.SetTheory.Internal
