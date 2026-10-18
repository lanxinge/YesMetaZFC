import YesMetaZFC.Model.SetTheory.Internal.RelationEvaluation
import YesMetaZFC.Model.SetTheory.ProjectBounded

/-! # 共同低层实现图的有界公式保持

完整前驱方程把原关系中的有界量词见证回收到同一实际低层。
因此函数、求值和复合都按原固定公式传输，无须先塌缩整个关系模型。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem rr_realize_delta_l {Γ Y S k : M.Domain} (hΓ : M.TransitiveSet Γ)
    (nx : Nonempty {x // M.mem x Γ}) (ny : ∃ y, M.mem y Y)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (pred : ∀ x a, M.PairMember I x a k → ∀ b,
      M.PairMember I b a S ↔ ∃ y, M.mem y x ∧ M.PairMember I y b k)
    {n} (φ : Formula 1 n) (closed : φ.FreeClosed) (delta : φ.IsDelta0)
    (ρ : Env (rt_model_l Γ nx) n) (η : Env (smdl_structure_l I (R := S) ny) n)
    (params : ∀ i, M.PairMember I (ρ.bound i).val (η.bound i).val k) :
    Formula.satisfies (image_env_l Subtype.val ρ) φ ↔ Formula.satisfies η φ := by
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice (fun x : {x // M.mem x Γ} => fk.1.2.2 x.val x.property)
  let e : (rt_model_l Γ nx).Domain → (smdl_structure_l I (R := S) ny).Domain := fun x => ⟨f x, (hf x).1⟩
  have injective : Function.Injective e := by
    intro x y eq
    have eq : f x = f y := congrArg Subtype.val eq
    exact Subtype.ext (fk.2 x.val y.val (f y) (eq ▸ (hf x).2) (hf y).2)
  have member (a : (rt_model_l Γ nx).Domain) (b : (smdl_structure_l I (R := S) ny).Domain) :
      (smdl_structure_l I (R := S) ny).mem b (e a) ↔
        ∃ x : (rt_model_l Γ nx).Domain, (rt_model_l Γ nx).mem x a ∧ e x = b := by
    apply (pred a.val (f a) (hf a).2 b.val).trans
    exact ⟨fun ⟨x, hx, hxb⟩ => ⟨⟨x, hΓ a.val a.property x hx⟩, hx,
      Subtype.ext (fk.1.1.2 x _ b.val (hf ⟨x, hΓ a.val a.property x hx⟩).2 hxb)⟩,
      fun ⟨x, hx, eq⟩ => ⟨x.val, hx, congrArg Subtype.val eq ▸ (hf x).2⟩⟩
  apply (rt_model_delta_l hΓ nx delta ρ).symm.trans ((delta0_image_l e injective member delta ρ).trans ?_)
  exact Formula.closed_env_l φ closed (funext fun i =>
    Subtype.ext (fk.1.1.2 _ _ _ (hf (ρ.bound i)).2 (params i)))

theorem rr_realize_function_l (hM : Extensional M) {Γ Y S k D E t : M.Domain}
    (hΓ : M.TransitiveSet Γ) (ny : ∃ y, M.mem y Y) (ext : Rf_ext_d I Y S)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (pred : ∀ x a, M.PairMember I x a k → ∀ b,
      M.PairMember I b a S ↔ ∃ y, M.mem y x ∧ M.PairMember I y b k)
    (d e p : (smdl_structure_l I (R := S) ny).Domain)
    (hD : M.PairMember I D d.val k) (hE : M.PairMember I E e.val k) (ht : M.PairMember I t p.val k)
    (ft : Fn0_d E D t) : Fn0_d e d p ∧ ∀ s r x y,
      Rd_entry_d s r t → M.PairMember I s x k → M.PairMember I r y k → Rf_val_d I Y S x y p.val := by
  let nx : Nonempty {x // M.mem x Γ} := ⟨⟨D, fk.1.input_mem_of_pairMember hD⟩⟩
  let D' : (rt_model_l Γ nx).Domain := ⟨D, fk.1.input_mem_of_pairMember hD⟩
  let E' : (rt_model_l Γ nx).Domain := ⟨E, fk.1.input_mem_of_pairMember hE⟩
  let t' : (rt_model_l Γ nx).Domain := ⟨t, fk.1.input_mem_of_pairMember ht⟩
  have en := ext.native_l I ny
  have transfer := rr_realize_delta_l I hΓ nx ny fk pred (fn0_m (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (fn0_delta_l ..)
    (⟨Fin.cases t' (Fin.cases D' (fun _ => E')), fun _ => D'⟩ : Env (rt_model_l Γ nx) 3)
    (⟨Fin.cases p (Fin.cases d (fun _ => e)), fun _ => d⟩ : Env (smdl_structure_l I (R := S) ny) 3)
    (Fin.cases ht (Fin.cases hD (fun _ => hE)))
  refine ⟨(fn0_sat_l en ..).mp (transfer.mp ((fn0_sat_l hM ..).mpr ft)), fun s r x y hsr hsx hry => ?_⟩
  let s' : (rt_model_l Γ nx).Domain := ⟨s, fk.1.input_mem_of_pairMember hsx⟩
  let r' : (rt_model_l Γ nx).Domain := ⟨r, fk.1.input_mem_of_pairMember hry⟩
  let x' : (smdl_structure_l I (R := S) ny).Domain := ⟨x, fk.1.output_mem_of_pairMember hsx⟩
  let y' : (smdl_structure_l I (R := S) ny).Domain := ⟨y, fk.1.output_mem_of_pairMember hry⟩
  have read := rr_realize_delta_l I hΓ nx ny fk pred (rd_entry0_m (.bound 2) (.bound 1) .newest)
    (by simp -implicitDefEqProofs) (rd_entry0_delta_l ..)
    (⟨Fin.cases t' (Fin.cases r' (fun _ => s')), fun _ => D'⟩ : Env (rt_model_l Γ nx) 3)
    (⟨Fin.cases p (Fin.cases y' (fun _ => x')), fun _ => d⟩ : Env (smdl_structure_l I (R := S) ny) 3)
    (Fin.cases ht (Fin.cases hry (fun _ => hsx)))
  exact (rf_val_native_l I ny en x' y' p).mpr
    ((rd_entry0_sat_l en ..).mp (read.mp ((rd_entry0_sat_l hM ..).mpr hsr)))

end YesMetaZFC.SetTheory.Internal
