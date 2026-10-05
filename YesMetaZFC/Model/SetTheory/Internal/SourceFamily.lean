import YesMetaZFC.Model.SetTheory.Internal.UniformizationSource

/-! # 有界分离族的源内函数图

先把各行的成员关系放入已有乘积，再取实际纤维族。函数值是这些纤维，
所以不要求源拥有完整幂集，也不对任意定义域作无界统一化。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem sc_fiber_function_l {ω c X R D P : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    (hD : M.mem D X) (hP : M.mem P X) : ∃ F C, M.mem F X ∧ M.mem C X ∧ Fn0_d D C F ∧
      ∀ d t, Rd_entry_d d t F ↔ M.mem d D ∧ Rd_fiber_d P d t := by
  obtain ⟨C, hC, fibers⟩ := theory.algebra.fibers P D hP hD
  let φ : BinarySchema 1 := { body := rd_fiber0_m (.bound 2) (.bound 1) .newest }
  let ρ : Env M 1 := ⟨fun _ => P, fun _ => P⟩
  have sat d t : φ.denote ρ d t ↔ Rd_fiber_d P d t := rd_fiber0_sat_l hZF.1 ..
  obtain ⟨F, hF, hf, select⟩ := sc_uniform_source_l hZF hω hX hm theory φ (rd_fiber0_delta_l ..)
    ρ (fun _ => hP) hD hC (fun d hd => by
      obtain ⟨t, ht⟩ := rd_fiber_exists_l (ZF.modelsKP hZF) P d
      exact ⟨t, (fibers t).mpr ⟨d, hd, ht⟩, (sat d t).mpr ht⟩)
  refine ⟨F, C, hF, hC, hf, fun d t => ⟨fun h => ⟨(hf.bound_l h).1, (sat d t).mp (select d t h)⟩, ?_⟩⟩
  rintro ⟨hd, ht⟩
  obtain ⟨u, _, hdu⟩ := hf.2.1 d hd
  exact hZF.1.eq_of_same_members u t (fun x => ((sat d u).mp (select d u hdu) x).trans (ht x).symm) ▸ hdu

theorem sc_separation_function_l {ω c X R D A : M.Domain} (hω : M.IsOmega ω)
    (hX : M.TransitiveSet X) (hm : Smem_d I c X R) (theory : Sc_theory_d I ω X R)
    {p} (φ : BinarySchema p) (hd : φ.body.IsDelta0) (ρ : Env M p) (hρ : ∀ i, M.mem (ρ.bound i) X)
    (hD : M.mem D X) (hA : M.mem A X) : ∃ F C, M.mem F X ∧ M.mem C X ∧ Fn0_d D C F ∧
      ∀ d t, Rd_entry_d d t F → ∀ x, M.mem x t ↔ M.mem x A ∧ φ.denote ρ d x := by
  obtain ⟨P, hPX, product⟩ := theory.algebra.product A D hA hD
  let e : Fin (p+2) → Fin (p+5) := Fin.cases 1 (Fin.cases 0 (fun i => i.succ.succ.succ.succ.succ))
  let η := (ρ.push A).push D
  let ψ : UnarySchema (p+2) := {
    body := Formula.existsMem (.bound 2) (Formula.existsMem (.bound 2)
      (.conj (kpair0_m (.bound 2) (.bound 1) .newest) (φ.body.rename e)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed] }
  have point q x d : Formula.satisfies (((η.push q).push x).push d) (φ.body.rename e) ↔ φ.denote ρ d x :=
    (Formula.satisfies_rename ..).trans (Formula.closed_env_l φ.body φ.freeClosed
      (funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))))
  have sat q : ψ.denote η q ↔ ∃ x, M.mem x A ∧ ∃ d, M.mem d D ∧ KPair_d M q x d ∧ φ.denote ρ d x := by
    simp only [ψ, UnarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      kpair0_sat_l hZF.1, point]; rfl
  obtain ⟨Q, hQX, spec⟩ := sc_separate_source_l I hZF hω hX hm theory ψ
    (.existsMem _ (.existsMem _ (.conj (kpair0_delta_l ..) (hd.rename_l e)))) η
    (Fin.cases hD (Fin.cases hA hρ)) hPX
  obtain ⟨F, C, hF, hC, hf, fibers⟩ := sc_fiber_function_l hZF hω hX hm theory hD hQX
  refine ⟨F, C, hF, hC, hf, fun d t hdt x => ((fibers d t).mp hdt).2 x |>.trans ⟨?_, ?_⟩⟩
  · rintro ⟨q, hq, hqQ⟩
    obtain ⟨a, ha, b, _, code, ht⟩ := (sat q).mp ((spec q).mp hqQ).2
    obtain ⟨rfl, rfl⟩ := kpair_injective_l M code hq
    exact ⟨ha, ht⟩
  · rintro ⟨hx, ht⟩
    obtain ⟨q, hq⟩ := (kp_pair_l (ZF.modelsKP hZF)).total x d
    exact ⟨q, hq, (spec q).mpr ⟨(product q).mpr ⟨x, hx, d, (hf.bound_l hdt).1, hq⟩,
      (sat q).mpr ⟨x, hx, d, (hf.bound_l hdt).1, hq, ht⟩⟩⟩

end YesMetaZFC.SetTheory.Internal
