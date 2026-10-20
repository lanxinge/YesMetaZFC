import YesMetaZFC.Model.SetTheory.Internal.RelationRealization
import YesMetaZFC.Model.SetTheory.Internal.RelationSubset
import YesMetaZFC.SetTheory.CumulativeRelativeRestriction

/-! # 原关系共同低层的整个相对秩历史

低层中的参数由完整前驱图解释。低层外的新对象若能参与幂集递归，
子集封闭便将其回收到低层；因此原全称秩证书对所有原关系对象成立。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

omit hZF in
def Rr_rank_d (Kp : kpair_convention_l.Interpretation M) (Y S a v : M.Domain) : Prop :=
  ∃ ha : M.mem a Y, ∃ hv : M.mem v Y,
    Formula.satisfies (⟨Fin.cases ⟨v, hv⟩ (fun _ => ⟨a, ha⟩), fun _ => ⟨a, ha⟩⟩ :
      Env (smdl_structure_l Kp (R := S) ⟨a, ha⟩) 2) (v_sigma_m (.bound 1) .newest)

/-- 低层中较早的相对秩段本身对子集封闭，且其全部新成员仍有内部编号。 -/
theorem rr_rank_low_l {Γ Y S H k α V v : M.Domain}
    (hΓ : M.TransitiveSet Γ) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ z, Rd_entry_d z H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x z k)
    (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
    (closed : Rr_closed_d I Y S H) (small : Rr_small_d I Y S H)
    (hV : M.mem V Γ) (rank : Vr_d Γ α V) (hVv : Rd_entry_d V v k) :
    Rr_closed_d I Y S v ∧ Rr_small_d I Y S v := by
  refine ⟨fun a b ha hb hav sub => ?_, fun a ha hav => ?_⟩
  · obtain ⟨x, hx, hxa⟩ := (pred V v hVv a).mp hav
    obtain ⟨A, hA, hAb, bound⟩ := rr_capture_l I closed hΓ fk image pred hxa hb sub
    exact (pred V v hVv b).mpr ⟨A, rank.subset_mem_l hΓ hV hx hA bound, hAb⟩
  · obtain ⟨x, hx, hxa⟩ := (pred V v hVv a).mp hav
    exact small a ha ((image a).mpr ⟨x, hΓ V hV x hx, hxa⟩)

theorem rr_realize_rank_l {c Y S Γ H k α V : M.Domain}
    (model : Smdl_d I c Y S) (ext : Rf_ext_d I Y S) (hΓ : M.TransitiveSet Γ)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ z, Rd_entry_d z H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x z k)
    (pred : ∀ x z, Rd_entry_d x z k → ∀ w, Rd_entry_d w z S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y w k)
    (closed : ∀ a b, M.mem a Y → M.mem b Y → Rd_entry_d a H S →
      (∀ x, M.mem x Y → Rd_entry_d x b S → Rd_entry_d x a S) → Rd_entry_d b H S)
    (a v : (smdl_structure_l I (R := S) model.2.1).Domain)
    (hα : Rd_entry_d α a.val k) (hV : Rd_entry_d V v.val k) (rank : Vr_d Γ α V) :
    Formula.satisfies (⟨Fin.cases v (fun _ => a), fun _ => a⟩ :
      Env (smdl_structure_l I (R := S) model.2.1) 2) (v_sigma_m (.bound 1) .newest) := by
  have hαΓ := fk.1.input_mem_of_pairMember hα
  have hVΓ := fk.1.input_mem_of_pairMember hV
  let nx : Nonempty {x // M.mem x Γ} := ⟨⟨α, hαΓ⟩⟩
  have en := ext.native_l I model.2.1
  obtain ⟨B, F, hBΓ, hFΓ, cert⟩ := rank
  obtain ⟨B', hB', hBB⟩ := fk.1.2.2 B hBΓ
  obtain ⟨F', hF', hFF⟩ := fk.1.2.2 F hFΓ
  let b : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨B', hB'⟩
  let f : (smdl_structure_l I (R := S) model.2.1).Domain := ⟨F', hF'⟩
  let η : Env (smdl_structure_l I (R := S) model.2.1) 2 := ⟨Fin.cases v (fun _ => a), fun _ => a⟩
  let ρ : Env (rt_model_l Γ nx) 2 := ⟨Fin.cases ⟨V, hVΓ⟩ (fun _ => ⟨α, hαΓ⟩), fun _ => ⟨α, hαΓ⟩⟩
  let φ : Formula 1 5 := vc_matrix_m (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest
  have read t (ht : M.mem t Γ) (z : (smdl_structure_l I (R := S) model.2.1).Domain) (htz : Rd_entry_d t z.val k) :
      Formula.satisfies (((η.push b).push f).push z) φ := by
    have transfer := rr_realize_delta_l I hΓ nx model.2.1 fk pred φ (by simp -implicitDefEqProofs [φ])
      (vc_matrix_delta_l ..) (((ρ.push ⟨B, hBΓ⟩).push ⟨F, hFΓ⟩).push ⟨t, ht⟩)
      (((η.push b).push f).push z) (Fin.cases htz (Fin.cases hFF (Fin.cases hBB (Fin.cases hV (fun _ => hα)))))
    exact transfer.mp ((vc_matrix_sat_l (ZF.modelsKP hZF) ..).mpr (cert t ht))
  have down (z w : (smdl_structure_l I (R := S) model.2.1).Domain)
      (hz : Rd_entry_d z.val H S) (hw : Rd_entry_d w.val z.val S) : Rd_entry_d w.val H S := by
    obtain ⟨x, hx, hxz⟩ := (image z.val).mp hz
    obtain ⟨y, hy, hyw⟩ := (pred x z.val hxz w.val).mp hw
    exact (image w.val).mpr ⟨y, hΓ x hx y hy, hyw⟩
  have bH := (image b.val).mpr ⟨B, hBΓ, hBB⟩
  have vH := (image v.val).mpr ⟨V, hVΓ, hV⟩
  simp only [v_sigma_m, Formula.satisfies_exists_iff, Formula.satisfies_forall_iff]
  refine ⟨b, f, fun z => ?_⟩
  by_cases hz : Rd_entry_d z.val H S
  · obtain ⟨t, ht, htz⟩ := (image z.val).mp hz
    exact read t ht z htz
  · have outside (β W : (smdl_structure_l I (R := S) model.2.1).Domain) (hW : Rd_entry_d W.val H S) :
        Vc_step_d β b f W z := by
      refine iff_of_false (fun h => hz (down W z hW h)) ?_
      rintro ⟨γ, _, U, hU, _, sub⟩
      exact hz (closed U.val z.val U.property z.property (down b U bH hU) (fun x hx => sub ⟨x, hx⟩))
    have base := read V hVΓ v hV
    simp only [φ, vc_matrix_m, Formula.satisfies_conj_iff, fn0_sat_l en,
      Formula.satisfies_forallMem_iff, Formula.satisfies_imp_iff, rd_entry0_sat_l en, vc_step_sat_l en] at base ⊢
    exact ⟨base.1, base.2.1, fun β _ W hW _ => outside β W (down b W bH hW), outside a v vH⟩

end YesMetaZFC.SetTheory.Internal
