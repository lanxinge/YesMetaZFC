import YesMetaZFC.Model.SetTheory.Relations.OmegaCut
import YesMetaZFC.Model.SetTheory.Relations.RecordImage
import YesMetaZFC.Model.SetTheory.Source.ClosureSyntax
import YesMetaZFC.Model.SetTheory.Internal.MembershipSlice

/-! # 完整前驱图在两侧原切片上保持全部公式

完整值域把实际图变成两个切片之间的同构。两侧载体保持原关系，
量词遍历各自整个切片，不把完整公式降成只在部分参数上成立的有界结论。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

theorem rr_native_slice_l {N R Γ C W t : M.Domain}
    (nx : ∃ x, M.mem x N) (ny : ∃ y, M.mem y C)
    (U : (smdl_structure_l I (R := R) nx).Domain) (V : (smdl_structure_l I (R := W) ny).Domain)
    (nu : Nonempty {x // (smdl_structure_l I (R := R) nx).mem x U})
    (nv : Nonempty {y // (smdl_structure_l I (R := W) ny).mem y V})
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ M.PairMember I x U.val R)
    (ft : M.IsSetInjectionFromTo I t Γ C)
    (image : ∀ E, M.PairMember I E V.val W ↔ ∃ x, M.mem x Γ ∧ M.PairMember I x E t)
    (pred : ∀ x E, M.PairMember I x E t → ∀ P,
      M.PairMember I P E W ↔ ∃ y, M.PairMember I y x R ∧ M.PairMember I y P t)
    {n} (φ : Formula 1 n) (closed : φ.FreeClosed)
    (ρ : Env (rt_model_l U nu) n) (σ : Env (rt_model_l V nv) n)
    (points : ∀ i, M.PairMember I (ρ.bound i).val.val (σ.bound i).val.val t) :
    Formula.satisfies ρ φ ↔ Formula.satisfies σ φ := by
  obtain ⟨f, hf⟩ := Classical.axiomOfChoice (fun x : (rt_model_l U nu).Domain =>
    ft.1.2.2 x.val.val ((carrier x.val.val).mpr ⟨x.val.property, x.property⟩))
  let e : (rt_model_l U nu).Domain → (rt_model_l V nv).Domain := fun x =>
    ⟨⟨f x, (hf x).1⟩, (image (f x)).mpr ⟨x.val.val,
      (carrier x.val.val).mpr ⟨x.val.property, x.property⟩, (hf x).2⟩⟩
  have onto : Function.Surjective e := by
    intro y
    obtain ⟨x, hx, hxy⟩ := (image y.val.val).mp y.property
    let a : (rt_model_l U nu).Domain := ⟨⟨x, ((carrier x).mp hx).1⟩, ((carrier x).mp hx).2⟩
    exact ⟨a, Subtype.ext (Subtype.ext (ft.1.1.2 x (f a) y.val.val (hf a).2 hxy))⟩
  have atoms x y : (rt_model_l U nu).mem x y ↔ (rt_model_l V nv).mem (e x) (e y) := by
    apply Iff.symm
    apply (pred y.val.val (f y) (hf y).2 (f x)).trans
    refine ⟨?_, fun h => ⟨x.val.val, h, (hf x).2⟩⟩
    rintro ⟨z, hz, hzx⟩
    change M.PairMember I x.val.val y.val.val R
    rw [← ft.2 z x.val.val (f x) hzx (hf x).2]
    exact hz
  exact (formula_image_l e onto atoms φ ρ).trans
    (Formula.closed_env_l φ closed (funext fun i =>
      Subtype.ext (Subtype.ext (ft.1.1.2 _ _ _ (hf (ρ.bound i)).2 (points i)))))

theorem rr_native_relative_l {N R Γ C W t : M.Domain}
    (nx : ∃ x, M.mem x N) (ny : ∃ y, M.mem y C)
    (U : (smdl_structure_l I (R := R) nx).Domain) (V : (smdl_structure_l I (R := W) ny).Domain)
    (ut : (smdl_structure_l I (R := R) nx).TransitiveSet U)
    (vt : (smdl_structure_l I (R := W) ny).TransitiveSet V)
    (nu : Nonempty {x // (smdl_structure_l I (R := R) nx).mem x U})
    (nv : Nonempty {y // (smdl_structure_l I (R := W) ny).mem y V})
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ M.PairMember I x U.val R)
    (ft : M.IsSetInjectionFromTo I t Γ C)
    (image : ∀ E, M.PairMember I E V.val W ↔ ∃ x, M.mem x Γ ∧ M.PairMember I x E t)
    (pred : ∀ x E, M.PairMember I x E t → ∀ P,
      M.PairMember I P E W ↔ ∃ y, M.PairMember I y x R ∧ M.PairMember I y P t)
    {n} (φ : Formula 1 n) (closed : φ.FreeClosed) (v w : Fin n → M.Domain)
    (points : ∀ i, M.PairMember I (v i) (w i) t) :
    Rr_truth_d I N R (lr_rel_m φ .newest (fun i => .bound i.succ)) (Fin.cases U.val v) ↔
      Rr_truth_d I C W (lr_rel_m φ .newest (fun i => .bound i.succ)) (Fin.cases V.val w) := by
  let ρ : Env (rt_model_l U nu) n := ⟨fun i =>
    ⟨⟨v i, ((carrier (v i)).mp (ft.1.input_mem_of_pairMember (points i))).1⟩,
      ((carrier (v i)).mp (ft.1.input_mem_of_pairMember (points i))).2⟩,
    fun _ => Classical.choice nu⟩
  let σ : Env (rt_model_l V nv) n := ⟨fun i =>
    ⟨⟨w i, ft.1.output_mem_of_pairMember (points i)⟩,
      (image (w i)).mpr ⟨v i, ft.1.input_mem_of_pairMember (points i), points i⟩⟩,
    fun _ => Classical.choice nv⟩
  let ε := (image_env_l Subtype.val ρ).push U
  let η := (image_env_l Subtype.val σ).push V
  have rel := lr_rel_closed_l φ closed .newest (fun i => .bound i.succ) rfl (fun _ => rfl)
  have left := (rr_truth_native_l I nx _ rel ε.bound).trans
    (Formula.closed_env_l _ rel (η := ε) rfl)
  have right := (rr_truth_native_l I ny _ rel η.bound).trans
    (Formula.closed_env_l _ rel (η := η) rfl)
  have lv : (fun i => (ε.bound i).val) = Fin.cases U.val v := funext (Fin.cases rfl (fun _ => rfl))
  have rv : (fun i => (η.bound i).val) = Fin.cases V.val w := funext (Fin.cases rfl (fun _ => rfl))
  rw [lv] at left
  rw [rv] at right
  exact left.trans ((sc_relative_sat_l ut nu φ closed ρ ε .newest (fun i => .bound i.succ) rfl (fun _ => rfl)).trans
    ((rr_native_slice_l I nx ny U V nu nv carrier ft image pred φ closed ρ σ points).trans
      ((sc_relative_sat_l vt nv φ closed σ η .newest (fun i => .bound i.succ) rfl (fun _ => rfl)).symm.trans right.symm)))

end YesMetaZFC.SetTheory.Internal

/-! ## native slice 到实际隶属载体的公式运输

`rr_native_slice_l` 只在两个原生切片之间运输闭公式。
当目标载体带有 `Smem_d` 证书时，`Smem_d.slice_formula_l` 可以把目标侧
原生赋值继续还原到实际成员关系载体。该组合不把一般 `Smdl_d` 误当成
外部成员关系。 -/
namespace YesMetaZFC.SetTheory.Internal

open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

theorem rr_native_slice_smem_l
    (I : kpair_convention_l.Interpretation M)
    {N R P S Γ t d : M.Domain}
    (nx : ∃ x, M.mem x N) (ny : ∃ y, M.mem y P)
    {U : (smdl_structure_l I (R := R) nx).Domain}
    {V : (smdl_structure_l I (R := S) ny).Domain}
    (nu : Nonempty {x // (smdl_structure_l I (R := R) nx).mem x U})
    (nv : Nonempty {y // (smdl_structure_l I (R := S) ny).mem y V})
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ M.PairMember I x U.val R)
    (ft : M.IsSetInjectionFromTo I t Γ P)
    (image : ∀ E, M.PairMember I E V.val S ↔ ∃ x, M.mem x Γ ∧ M.PairMember I x E t)
    (pred : ∀ x E, M.PairMember I x E t → ∀ Q,
      M.PairMember I Q E S ↔ ∃ y, M.PairMember I y x R ∧ M.PairMember I y Q t)
    {n : Nat} (φ : Formula 1 n) (closed : φ.FreeClosed)
    (ρ : Env (rt_model_l U nu) n)
    (σ : Env (rt_model_l V nv) n)
    (points : ∀ i, M.PairMember I (ρ.bound i).val.val (σ.bound i).val.val t)
    (model : Smem_d I d P S)
    (inside : M.MemberSubset V.val P)
    (nvOuter : Nonempty {y // M.mem y V.val}) :
    Formula.satisfies ρ φ ↔
      Formula.satisfies (model.slice_env_d I V nv nvOuter σ) φ := by
  exact (rr_native_slice_l I nx ny U V nu nv carrier ft image pred φ closed ρ σ points).trans
    (model.slice_formula_l I V inside nv nvOuter φ σ)

end YesMetaZFC.SetTheory.Internal
