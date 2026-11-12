import YesMetaZFC.Model.SetTheory.Relations.Parity
import YesMetaZFC.Model.SetTheory.Internal.RelativizationCorrect
import YesMetaZFC.Model.SetTheory.Relations.Small

/-! # 完整低层实现上的全内部程序解释

实现图的实际值域与原低层关系同构；限制编译器的守卫取高模型中的层对象。
源关系不必是背景隶属。同构和限制两步都量化全部内部程序，故非标准程序
不需解码成宿主语法树，也不要求源切片在背景中传递。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rr_program_l {ω Γ Y S H k R E D F n r b m G T u f g : M.Domain}
    (hω : M.IsOmega ω) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (atoms : ∀ a b x y, Rd_entry_d a x k → Rd_entry_d b y k →
      (Rd_entry_d a b R ↔ Rd_entry_d x y S))
    (hE : M.IsFunctionSpace I E ω Γ) (hD : M.IsFunctionSpace I D ω Y)
    (hF : Sfm_d I ω n F) (hr : M.mem r n) (hb : M.mem b ω) (bound : Sbound_d I F b)
    (state : Sr_state_d I ω b F n m G T) (root : Rd_entry_d r u T)
    (hf : M.mem f E) (hg : M.mem g D) (guard : Rd_entry_d b H g)
    (params : ∀ i x y, M.mem i b → Rd_entry_d i x f → Rd_entry_d x y k → Rd_entry_d i y g) :
    Ssat_d I Γ R E F n r f ↔ Ssat_d I Y S D G m u g := by
  obtain ⟨A, range⟩ := ZF.exists_range_of_setFunction hZF I fk.1.1 fk.1.2.1
  have fn : M.IsSetFunctionFromTo I k Γ A :=
    ⟨fk.1.1, fk.1.2.1, fun x hx =>
      (fk.1.2.2 x hx).imp fun y hy => ⟨(range y).mpr ⟨x, hy.2⟩, hy.2⟩⟩
  have bij : M.IsSetBijectionFromTo I k Γ A :=
    ⟨⟨fn, fk.2⟩, fun y hy => ((range y).mp hy).elim fun x hx =>
      ⟨x, fn.input_mem_of_pairMember hx, hx⟩⟩
  obtain ⟨K, hK⟩ := ZF.exists_functionSpace hZF I ω A
  obtain ⟨v, fv, map⟩ := smap_assign_exists_l I hZF fn ((hE f).mp hf)
  have context : Sr_context_d I ω A S Y S H K D := by
    refine ⟨fun x hx => ((range x).mp hx).elim fun a ha => fk.1.output_mem_of_pairMember ha,
      fun _ _ _ _ => Iff.rfl, ?_, hK, hD⟩
    intro x _
    exact (image x).trans ⟨fun ⟨a, _, ha⟩ => (range x).mpr ⟨a, ha⟩,
      fun hx => ((range x).mp hx).elim fun a ha => ⟨a, fn.input_mem_of_pairMember ha, ha⟩⟩
  have agree : Senv_agree_d I b v g := by
    intro i y hi
    have hiω := hω.transitive (ZF.modelsKP hZF) b hb i hi
    obtain ⟨x, hx, hix⟩ := ((hE f).mp hf).2.2 i hiω
    obtain ⟨z, _, hxz⟩ := fn.2.2 x hx
    have hiv := map i hiω x z hix hxz
    have hig := params i x z hi hix hxz
    exact ⟨fun hy => fv.1.2 i y z hy hiv ▸ hig,
      fun hy => ((hD g).mp hg).1.2 i y z hy hig ▸ hiv⟩
  exact (smap_row_l I hZF bij atoms hE hK hF hr f v hf ((hK v).mpr fv) map).trans
    (state.correct_l I hZF hF bound context hr root v g ((hK v).mpr fv) hg guard agree)

end YesMetaZFC.SetTheory.Internal

/-! ## 新共同层的全内部分离

任意内部程序先限制到原关系层对象，再在高模型中分离。子集封闭把实际
分离集回收到同一切片，关系同构逐项读回全部成员。源侧也使用原关系；
全程保留原程序、原赋值和非标准长度，不要求源切片在背景中传递。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem rr_separation_l {ω c X R c' Y S q Γ H k T E F n r i f D : M.Domain}
    (hω : M.IsOmega ω) (mx : Smdl_d I c X R)
    (theory : Sc_theory_d I ω X R) (my : Smdl_d I c' Y S) (map : Smap_d I ω c c' X Y q)
    (hH : M.mem H Y) (fk : M.IsSetInjectionFromTo I k Γ Y)
    (image : ∀ y, Rd_entry_d y H S ↔ ∃ x, M.mem x Γ ∧ Rd_entry_d x y k)
    (atoms : ∀ a b x y, Rd_entry_d a x k → Rd_entry_d b y k →
      (Rd_entry_d a b T ↔ Rd_entry_d x y S))
    (closed : Rr_closed_d I Y S H)
    (hE : M.IsFunctionSpace I E ω Γ) (hF : Sfm_d I ω n F) (hr : M.mem r n)
    (hi : M.mem i ω) (hf : M.mem f E) (hD : M.mem D Γ) :
    ∃ A, M.mem A Γ ∧ Sr_sep_d I Γ T E F n r i f D A := by
  obtain ⟨b, hb, bound, hib, _⟩ := sbound_above_l I hZF hω hF hi hi
  obtain ⟨m, G, V, state⟩ := sr_compile_at_l I hZF hω hF hb
  obtain ⟨u, hu, hru⟩ := state.map.2.2 r hr
  obtain ⟨K, hK⟩ := ZF.exists_functionSpace hZF I ω Y
  obtain ⟨g, fg, assign⟩ := smap_assign_exists_l I hZF fk.1 ((hE f).mp hf)
  obtain ⟨h, gh, fh⟩ := senv_update_exists_l I hZF fg hb hH
  have hbg := (gh.2 b H).mpr (Or.inl ⟨rfl, rfl⟩)
  have hbi : b ≠ i := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) b (eq.symm ▸ hib)
  have compare x y (hx : M.mem x Γ) (hxy : Rd_entry_d x y k) v w
      (fv : Senv_update_d I f i x v) (hw : Senv_update_d I h i y w) :
      Ssat_d I Γ T E F n r v ↔ Ssat_d I Y S K G m u w := by
    have hy := fk.1.output_mem_of_pairMember hxy
    apply rr_program_l hZF hω fk image atoms hE hK hF hr hb bound state hru
      ((hE v).mpr (fv.function_l I ((hE f).mp hf) hi hx))
      ((hK w).mpr (hw.function_l I fh hi hy)) ((hw.2 b H).mpr (Or.inr ⟨hbi, hbg⟩))
    intro j z z' hj hjz hzz
    rcases (fv.2 j z).mp hjz with ⟨rfl, rfl⟩ | ⟨hji, hjz⟩
    · exact (hw.2 j z').mpr (Or.inl ⟨rfl, fk.1.1.2 z z' y hzz hxy⟩)
    · have hjb : j ≠ b := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZF) b (eq ▸ hj)
      exact (hw.2 j z').mpr (Or.inr ⟨hji, (gh.2 j z').mpr
        (Or.inr ⟨hjb, assign j (hω.transitive (ZF.modelsKP hZF) b hb j hj) z z' hjz hzz⟩)⟩)
  obtain ⟨d, hd, hDd⟩ := fk.1.2.2 D hD
  obtain ⟨A, hA, sep⟩ := sc_separation_raw_l I hZF hω mx my map theory
    hK state.program hu hi ((hK h).mpr fh) hd
  obtain ⟨B, hB, hBA⟩ := (image A).mp (closed d A hd hA ((image d).mpr ⟨D, hD, hDd⟩)
    (fun x hx hxa => ((sep x hx).mp hxa).1))
  refine ⟨B, hB, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := fk.1.2.2 x hx
  have truth :
      (∃ v, Senv_update_d I f i x v ∧ Ssat_d I Γ T E F n r v) ↔
      ∃ w, Senv_update_d I h i y w ∧ Ssat_d I Y S K G m u w := by
    constructor
    · rintro ⟨v, fv, valid⟩
      obtain ⟨w, hw, _⟩ := senv_update_exists_l I hZF fh hi hy
      exact ⟨w, hw, (compare x y hx hxy v w fv hw).mp valid⟩
    · rintro ⟨w, hw, valid⟩
      obtain ⟨v, fv, _⟩ := senv_update_exists_l I hZF ((hE f).mp hf) hi hx
      exact ⟨v, fv, (compare x y hx hxy v w fv hw).mpr valid⟩
  exact (atoms x B y A hxy hBA).trans
    ((sep y hy).trans (and_congr (atoms x D y d hxy hDd).symm truth.symm))

end YesMetaZFC.SetTheory.Internal
