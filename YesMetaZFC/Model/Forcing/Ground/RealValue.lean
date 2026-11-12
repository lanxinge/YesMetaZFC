import YesMetaZFC.Model.Forcing.Ground.RealCodeImage
import YesMetaZFC.Model.Forcing.Ground.ProductProjection
import YesMetaZFC.SetTheory.FunctionConstruction

/-! # 有限集合模型泛型扩张的每个实数都有实际背景图

任取商扩张中的实数，用原名字的关系力迫在背景 ω² 中分离其图。
真值定理证明全定义性及逐点唯一性，故覆盖全部扩张实数，而非仅已编码实数。
-/
namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.InnerModel SetTheory.Internal
universe u
variable {M : Structure.{u}} (hM : M.Models ZF) {c X R : M.Domain}
  (source : Smem_d (kp_pair_l (ZF.modelsKP hM)) c X R) (trans : M.TransitiveSet X)
  (native : (smdl_structure_l (kp_pair_l (ZF.modelsKP hM)) (R := R) source.1.2.1).Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
include trans native

theorem real_values_background_l
    {ω B T : (smdl_structure_l I (R := R) source.1.2.1).Domain} {H : M.Domain}
    (O : Cond_order_d (smdl_structure_l I (R := R) source.1.2.1) B T B)
    (generic : Gset_d B.val T.val B.val X H) :
    let N := smdl_structure_l I (R := R) source.1.2.1
    let G : N.Domain → Prop := fun p => M.mem p.val H
    let E := extension_l N native B T B G
    ∃ j : N.Domain → E.Domain, (∀ a, Gval_d N B T B G a (j a)) ∧
      ∀ y, Fn0_d (j ω) (j ω) y → ∃ x,
        Fn0_d ω.val ω.val x ∧ Fn_bg_d X B.val T.val B.val ω.val ω.val H x ∧ Fn_read_d Subtype.val j y x := by
  dsimp only
  let N := smdl_structure_l I (R := R) source.1.2.1
  let G : N.Domain → Prop := fun p => M.mem p.val H
  let E := extension_l N native B T B G
  have g := ((source.generic_code_l I hM.1 trans (ZF.modelsKP native) B T B H).mp generic).2
  have hE := preserves_zf_l O native g
  have inj : Function.Injective (Subtype.val : N.Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have full := smem_full_l I source trans
  have mem {a b : N.Domain} : M.mem a.val b.val ↔ N.mem a b := image_member_l (M := N) (N := M) Subtype.val inj full
  obtain ⟨b,hb⟩ := g.inhabited
  obtain ⟨j,checks,jfull,ji⟩ := check_map_l O native g hb
  have ground a := (gval_check_map_l O native g hb j checks a (j a)).mpr rfl
  refine ⟨j,ground,fun y real => ?_⟩
  obtain ⟨τ,_,value⟩ := value_name_l y
  let ρ : Env M 7 := ⟨fun i => [X,B.val,T.val,B.val,b.val,τ.val,H].get i,fun _ => X⟩
  let edge : Formula 1 10 := lr_rel_m nentry0_m (.bound 3)
    (fun i => .bound (([4,5,6,7,8,2,1,0] : List (Fin 10)).get i))
  have closed : edge.FreeClosed := lr_rel_closed_l nentry0_m nentry0_closed_l _ _ rfl (fun _ => rfl)
  let φ : BinarySchema 7 := {
    body := Formula.existsMem (.bound 2) (.conj (.mem .newest (.bound 9)) edge)
    freeClosed := ⟨⟨rfl,rfl⟩,⟨⟨rfl,rfl⟩,closed⟩⟩ }
  have decode (a d q : N.Domain) :
      Formula.satisfies (((ρ.push a.val).push d.val).push q.val) edge ↔ Nentry_d B T B b τ a d q := by
    let η : Env N 8 := ⟨fun i => [B,T,B,b,τ,a,d,q].get i,fun _ => τ⟩
    exact (lr_rel_decode_l I source.1 source.2 trans nentry0_m nentry0_closed_l η
      (((ρ.push a.val).push d.val).push q.val) (.bound 3)
      (fun i => .bound (([4,5,6,7,8,2,1,0] : List (Fin 10)).get i)) rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))))))).trans
      (nentry_sat_l native.1 η (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7))
  have truth (a d : N.Domain) : φ.denote ρ a.val d.val ↔ Entry_d E (j a) (j d) y := by
    apply Iff.trans ?_ (nentry_truth_l native O g hb value j checks a d)
    change (∃ q, M.mem q X ∧ M.mem q H ∧ Formula.satisfies (((ρ.push a.val).push d.val).push q) edge) ↔ _
    exact ⟨fun ⟨q,hq,hH,h⟩ => ⟨⟨q,hq⟩,hH,(decode a d ⟨q,hq⟩).mp h⟩,
      fun ⟨q,hq,h⟩ => ⟨q.val,q.property,hq,(decode a d q).mpr h⟩⟩
  obtain ⟨x,rel,graph⟩ := ZF.exists_setRelationOn_of_denote hM I φ ρ ω.val
  have fy := fn0_function_l (ZF.modelsKP hE) real
  have edges (a d : N.Domain) : Entry_d M a.val d.val x ↔ Entry_d E (j a) (j d) y := by
    apply (graph a.val d.val).trans
    refine ⟨fun h => (truth a d).mp h.2.2,fun h => ?_⟩
    exact ⟨mem.mpr ((image_member_l j ji jfull).mp (fy.input_mem_of_pairMember h)),
      mem.mpr ((image_member_l j ji jfull).mp (fy.output_mem_of_pairMember h)),(truth a d).mpr h⟩
  have read : Fn_read_d Subtype.val j y x := by
    intro a d
    constructor
    · intro h
      obtain ⟨a₀,_,rfl⟩ := (full ω a).mp ((graph a d).mp h).1
      obtain ⟨d₀,_,rfl⟩ := (full ω d).mp ((graph a₀.val d).mp h).2.1
      exact ⟨a₀,d₀,rfl,rfl,(edges a₀ d₀).mp h⟩
    · rintro ⟨a₀,d₀,rfl,rfl,h⟩
      exact (edges a₀ d₀).mpr h
  have rows a (ha : M.mem a ω.val) : ∃ d, M.mem d ω.val ∧ Entry_d M a d x := by
    obtain ⟨a₀,ha₀,rfl⟩ := (full ω a).mp ha
    obtain ⟨d,hd,ad⟩ := fy.2.2 (j a₀) ((image_member_l j ji jfull).mpr ha₀)
    obtain ⟨d₀,hd₀,rfl⟩ := (jfull ω d).mp hd
    exact ⟨d₀.val,mem.mpr hd₀,(edges a₀ d₀).mpr ad⟩
  have fx : M.IsSetFunctionFromTo I x ω.val ω.val := by
    refine ⟨⟨rel.1,?_⟩,fun a => ⟨fun ha => (rows a ha).elim (fun d h => ⟨d,h.2⟩),
      fun ⟨d,ad⟩ => ((graph a d).mp ad).1⟩,rows⟩
    intro a d f ad af
    obtain ⟨a₀,d₀,ea,ed,old⟩ := (read a d).mp ad
    obtain ⟨a₁,f₀,ea',ef,new⟩ := (read a f).mp af
    have eq : a₁ = a₀ := Subtype.ext (ea'.trans ea.symm)
    subst a₁
    exact ed.symm.trans ((congrArg Subtype.val (ji (fy.1.2 (j a₀) (j d₀) (j f₀) old new))).trans ef)
  exact ⟨x,fn0_of_function_l (ZF.modelsKP hM) fx,
    (fn_bg_read_l I hM.1 source trans native.1 B T B ω ω H x).mpr
      (fn_code_of_value_l native O g Subtype.val j ground real read),read⟩

end YesMetaZFC.Model.Forcing.Internal
