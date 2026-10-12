import YesMetaZFC.Model.SetTheory.Internal.EmbeddingFixed
import YesMetaZFC.SetTheory.CumulativeRelativeAlgebra

/-! # 共同相对秩段的逐点固定

先在共同载体中比较两份原历史，再将源历史的像与目标历史比较。
低序数固定给出每个低层整体固定；对层号作强归纳，子集保持给出逐点固定。
不要求载体满足 ZF，也不预设临界点在背景中不可达。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Smap_d.rank_fixed_l {ω c d X R Y S j κ ℓ V : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S) (hj : Smap_d I ω c d X Y j)
    (hκ : Rd_entry_d κ ℓ j) (fixed : ∀ β, M.mem β κ → Rd_entry_d β β j)
    (hV : M.mem V X) (rx : Vr_d X κ V) (hV' : M.mem V Y) (ry : Vr_d Y κ V) :
    ∀ x, M.mem x V → Rd_entry_d x x j := by
  have vt := rx.transitive_l hZF hX hV
  obtain ⟨B, F, hB, hF, cx⟩ := rx
  obtain ⟨C, G, hC, _, cy⟩ := ry
  have ff := (cx V hV).2.1
  have gf := (cy V hV').2.1
  have ho := (cx V hV).1
  have low δ U (hu : Rd_entry_d δ U F) : M.mem U V :=
    ((cx U (hX B hB U (ff.bound_l hu).2)).2.2.2).mpr
      ⟨δ, (ff.bound_l hu).1, U, (ff.bound_l hu).2, hu, fun _ h => h⟩
  have low' δ U (hu : Rd_entry_d δ U G) : M.mem U V :=
    ((cy U (hY C hC U (gf.bound_l hu).2)).2.2.2).mpr
      ⟨δ, (gf.bound_l hu).1, U, (gf.bound_l hu).2, hu, fun _ h => h⟩
  have same := vc_history_eq_l hZF vt ff gf ho (fun _ h => h)
    (fun δ hδ U hu => ⟨low δ U hu, fun t ht =>
      (cx t (hX V hV t ht)).2.2.1 δ hδ U (ff.bound_l hu).2 hu⟩)
    (fun δ hδ U hu => ⟨low' δ U hu, fun t ht =>
      (cy t (hY V hV' t ht)).2.2.1 δ hδ U (gf.bound_l hu).2 hu⟩)
  obtain ⟨V', hV'Y, iV⟩ := hj.1.1.2.2 V hV
  obtain ⟨B', hB', iB⟩ := hj.1.1.2.2 B hB
  obtain ⟨F', _, iF⟩ := hj.1.1.2.2 F hF
  let ψ : Formula 1 5 := vc_matrix_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
  have tr := hj.forall_delta_l hZF hω hX hY mx my ψ (by simp -implicitDefEqProofs [ψ])
    (vc_matrix_delta_l ..) ⟨Fin.cases F (Fin.cases B (Fin.cases V (fun _ => κ))), fun _ => κ⟩
    ⟨Fin.cases F' (Fin.cases B' (Fin.cases V' (fun _ => ℓ))), fun _ => ℓ⟩
    (Fin.cases iF (Fin.cases iB (Fin.cases iV (fun _ => hκ))))
  simp only [ψ, vc_matrix_sat_l (ZF.modelsKP hZF)] at tr
  have ci := tr.mp cx
  have fi := (ci V' hV'Y).2.1
  have sub β (hβ : M.mem β κ) := (hj.member_l I hZF hω mx my (fixed β hβ) hκ).mp hβ
  have images := vc_history_eq_l hZF hY fi gf ho sub
    (fun δ hδ U hu => ⟨hY B' hB' U (fi.bound_l hu).2, fun t ht =>
      (ci t ht).2.2.1 δ (sub δ hδ) U (fi.bound_l hu).2 hu⟩)
    (fun δ hδ U hu => ⟨hY C hC U (gf.bound_l hu).2, fun t ht =>
      (cy t ht).2.2.1 δ hδ U (gf.bound_l hu).2 hu⟩)
  have level β (hβ : M.mem β κ) U (hu : Rd_entry_d β U F) : Rd_entry_d U U j := by
    obtain ⟨U', _, iU⟩ := hj.1.1.2.2 U (hX V hV U (low β U hu))
    obtain ⟨W, _, hw⟩ := gf.2.1 β hβ
    have hu' := (hj.entry_l hZF hω hX hY mx my (fixed β hβ) iU iF).mp hu
    exact ((images β hβ U' W hu' hw).trans (same β hβ U W hu hw).symm) ▸ iU
  let ρ : Env M 3 := ⟨Fin.cases κ (Fin.cases F (fun _ => j)), fun _ => κ⟩
  let φ : UnarySchema 3 := { body := .imp (.mem .newest (.bound 1)) (.forallE
    (.imp (rd_entry0_m (.bound 1) .newest (.bound 3))
      (Formula.forallMem .newest (rd_entry0_m .newest .newest (.bound 5))))) }
  have sat β : φ.denote ρ β ↔ M.mem β κ → ∀ U, Rd_entry_d β U F →
      ∀ x, M.mem x U → Rd_entry_d x x j := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_forall_iff, Formula.satisfies_forallMem_iff, rd_entry0_sat_l hZF.1]; rfl
  have point β (hβ : M.mem β κ) : ∀ U, Rd_entry_d β U F → ∀ x, M.mem x U → Rd_entry_d x x j := by
    apply (sat β).mp (ZF.mem_ind_l M hZF I φ ρ ?_ β) hβ
    intro β ih
    apply (sat β).mpr
    intro hβ U hu x hx
    have hxX := hX V hV x (vt U (low β U hu) x hx)
    obtain ⟨γ, hγ, W, _, hw, bound⟩ := ((cx x hxX).2.2.1 β hβ U (ff.bound_l hu).2 hu).mp hx
    exact hj.fixed_subset_l hZF hω hX hY mx my (level γ (ho.transitive β hβ γ hγ) W hw)
      ((sat γ).mp (ih γ hγ) (ho.transitive β hβ γ hγ) W hw) hxX bound
  intro x hx
  have hxX := hX V hV x hx
  obtain ⟨β, hβ, U, _, hu, bound⟩ := ((cx x hxX).2.2.2).mp hx
  exact hj.fixed_subset_l hZF hω hX hY mx my (level β hβ U hu) (point β hβ U hu) hxX bound

end YesMetaZFC.SetTheory.Internal
