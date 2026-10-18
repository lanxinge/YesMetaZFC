import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRawReduced
import YesMetaZFC.Model.SetTheory.Internal.RelationRealization
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.RelationMeasure
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.RelationProjection

/-! # 共同低层内实际有限支撑的原关系过渡

所属源构造有限坐标投影；共同相对秩段回收其图。完整前驱实现将同一图
读作原关系内部的函数，再由原扩展器协调律与两侧真实测度限制形成初等过渡。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}}
section
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ec_raw_push_l {ω c X R c' Y S j₀ κ L N F D E u v t P Q U V U' V' m n r a b : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (model : Smdl_d I c' Y S) (hj : Smap_d I ω c c' X Y j₀)
    (ext : Rf_ext_d I Y S) (d e p : (smdl_structure_l I (R := S) model.2.1).Domain)
    (fp : Fn0_d e d p) (fu : Fn0_d D Y u) (fv : Fn0_d E Y v) (ft : Fn0_d E D t)
    (dv : ∀ s x, Rd_entry_d s x v → Rd_entry_d x e.val S)
    (comm : ∀ s w x y, Rd_entry_d s w t → Rd_entry_d s x v → Rd_entry_d w y u → Rf_val_d I Y S x y p.val)
    (hP : Rt_source_d I Y S D u P) (hQ : Rt_source_d I Y S E v Q) (inside : M.MemberSubset P N)
    (us : ∀ A, M.mem A U' ↔ M.mem A P ∧ M.mem A U) (vs : ∀ A, M.mem A V' ↔ M.mem A Q ∧ M.mem A V)
    (coherent : Ec_source_d I ω κ L N F) (hm : M.mem m ω) (hn : M.mem n ω)
    (hr : Fn0_d m n r) (hb : Fn0_d n L b) (hra : Cp0_d m n L r b a)
    (haU : Rd_entry_d a U F) (hbV : Rd_entry_d b V F)
    (hD : Ep_space_d κ m D) (hE : Ep_space_d κ n E)
    (ts : ∀ s w, Rd_entry_d s w t ↔ M.mem s E ∧ Cp0_d m n κ r s w) : Push_d D E P Q U' V' t := by
  refine ⟨ft, fun A hA => ?_⟩
  obtain ⟨B, hB, pull⟩ := hP.pull_l hZF hω hX mx theory model hj ext d e p fp fu fv ft dv comm hQ hA
  have sub : M.MemberSubset A D := by
    obtain ⟨_, _, tr⟩ := (hP A).mp hA
    exact fun s hs => ((tr s).mp hs).1
  obtain ⟨B', spec, measure⟩ := coherent m n r b a U V A hm hn (inside A hA) hr hb hra hbV haU
    (fun s hs => (hD s).mp (sub s hs))
  have eq : B' = B := hZF.1.eq_of_same_members B' B fun s => (spec s).trans
    ⟨fun ⟨hs, w, hw, hsw⟩ => (pull s).mpr ⟨(hE s).mpr hs, w, hw, (ts s w).mpr ⟨(hE s).mpr hs, hsw⟩⟩,
      fun h => by
        obtain ⟨hs, w, hw, hsw⟩ := (pull s).mp h
        exact ⟨(hE s).mp hs, w, hw, ((ts s w).mp hsw).2⟩⟩
  subst B'
  exact ⟨B, hB, pull, ((vs B).trans (and_iff_right hB)).trans
    (measure.trans ((us A).trans (and_iff_right hA)).symm)⟩

end

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_raw_map_l {ω c X R c' Y S j₀ κ K L N R₀ F Γ γ k D E u v P Q U V U' V'
    m n r a b o₀ o₁ G₀ G₁ p₀ p₁ C₀ C₁ T₀ T₁ : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (mx : Smem_d I c X R)
    (theory : Sc_theory_d I ω X R) (collection : Sc_collection_d I ω X R)
    (model : Smdl_d I c' Y S) (hj : Smap_d I ω c c' X Y j₀)
    (owner : Ep_source_d hZF ω κ K N R₀) (hΓ : M.mem Γ N) (rank : Vr_d N γ Γ) (hγ : M.IsLimitOrdinal γ)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (pred : ∀ x a, Rd_entry_d x a k → ∀ z, Rd_entry_d z a S ↔ ∃ y, M.mem y x ∧ Rd_entry_d y z k)
    (d e μ₀ f₀ μ₁ f₁ : (smdl_structure_l I (R := S) model.2.1).Domain)
    (hDd : Rd_entry_d D d.val k) (hEe : Rd_entry_d E e.val k)
    (hu : M.IsRestrictionOf I u k D) (hv : M.IsRestrictionOf I v k E)
    (small₀ : Formula.satisfies (⟨Fin.cases μ₀ (Fin.cases d (fun _ => f₀)), fun _ => d⟩ :
      Env (smdl_structure_l I (R := S) model.2.1) 3) (sc_index_m .newest (.bound 1) (.bound 2)))
    (small₁ : Formula.satisfies (⟨Fin.cases μ₁ (Fin.cases e (fun _ => f₁)), fun _ => e⟩ :
      Env (smdl_structure_l I (R := S) model.2.1) 3) (sc_index_m .newest (.bound 1) (.bound 2)))
    (hP : Rt_source_d I Y S D u P) (hQ : Rt_source_d I Y S E v Q) (inside : M.MemberSubset P N)
    (hU : Rel_ultra_d D P U') (hV : Rel_ultra_d E Q V')
    (us : ∀ A, M.mem A U' ↔ M.mem A P ∧ M.mem A U) (vs : ∀ A, M.mem A V' ↔ M.mem A Q ∧ M.mem A V)
    (coherent : Ec_source_d I ω κ L N F) (hm : M.mem m ω) (hn : M.mem n ω)
    (hr : Fn0_d m n r) (hb : Fn0_d n L b) (hra : Cp0_d m n L r b a)
    (haU : Rd_entry_d a U F) (hbV : Rd_entry_d b V F) (hD : Ep_space_d κ m D) (hE : Ep_space_d κ n E)
    (inj : ∀ i j x, Rd_entry_d i x b → Rd_entry_d j x b → i = j)
    (hG₀ : ∀ g, M.mem g G₀ ↔ Fn0_d D Y g ∧
      ∃ B f : (smdl_structure_l I (R := S) model.2.1).Domain, Fn0_d d B f ∧
        ∀ s (x y : (smdl_structure_l I (R := S) model.2.1).Domain), Rd_entry_d s x.val u →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f))
    (hG₁ : ∀ g, M.mem g G₁ ↔ Fn0_d E Y g ∧
      ∃ B f : (smdl_structure_l I (R := S) model.2.1).Domain, Fn0_d e B f ∧
        ∀ s (x y : (smdl_structure_l I (R := S) model.2.1).Domain), Rd_entry_d s x.val v →
          (Rd_entry_d s y.val g ↔ Rd_entry_d x y f))
    (model₀ : Rp_model_d I D Y U' S o₀ G₀ p₀ C₀ T₀) (model₁ : Rp_model_d I E Y V' S o₁ G₁ p₁ C₁ T₁) :
    ∃ t H j, M.mem t Γ ∧ Fn0_d E D t ∧
      (∀ s w, Rd_entry_d s w t ↔ M.mem s E ∧ Cp0_d m n κ r s w) ∧
      M.IsSetFunctionFromTo I H G₀ G₁ ∧
      (∀ f g, Rd_entry_d f g H ↔ M.mem f G₀ ∧ M.mem g G₁ ∧ Cp0_d E D Y t f g) ∧
      Smap_d I ω o₀ o₁ C₀ C₁ j ∧ Rp_lift_d I H p₀ p₁ j ∧
      (∀ B C, Rd_entry_d B C j ↔ M.mem B C₀ ∧ M.mem C C₁ ∧ Ep_arrow_d ω κ L Y a b B C) ∧
      (∀ B C, Rd_entry_d B C j → Ep_lift_d ω κ L Y a b B C) ∧
      ∃ i₀ i₁, Smap_d I ω c' o₀ Y C₀ i₀ ∧ Smap_d I ω c' o₁ Y C₁ i₁ ∧
        (∀ x B, Rd_entry_d x B i₀ ↔ M.mem x Y ∧ ∃ f, M.mem f G₀ ∧ Rs_const_d D x f ∧ Rd_entry_d f B p₀) ∧
        (∀ x B, Rd_entry_d x B i₁ ↔ M.mem x Y ∧ ∃ f, M.mem f G₁ ∧ Rs_const_d E x f ∧ Rd_entry_d f B p₁) ∧
        ∀ x B C, Rd_entry_d x B i₀ → (Rd_entry_d B C j ↔ Rd_entry_d x C i₁) := by
  have trans := rank.transitive_l hZF owner.transitive hΓ
  have hDΓ := fk.1.input_mem_of_pairMember hDd
  have hEΓ := fk.1.input_mem_of_pairMember hEe
  obtain ⟨t, htN, ft, ts⟩ := owner.projection_l hZF hm hn hr hD hE
  have htΓ := rank.relation_mem_l hZF owner.transitive hΓ hγ hEΓ hDΓ htN ft.1
  obtain ⟨p, hp, htp⟩ := fk.1.2.2 t htΓ
  have ext : Rf_ext_d I Y S := hj.extensional_l hZF hω mx.1 model (rf_ext_mem_l I hZF.1 hX mx)
  obtain ⟨fp, read⟩ := rr_realize_function_l I hZF.1 trans model.2.1 ext fk pred d e ⟨p, hp⟩ hDd hEe htp ft
  have fu := fn0_of_function_l (ZF.modelsKP hZF) (hu.isSetFunctionFromTo fk.1 (trans D hDΓ))
  have fv := fn0_of_function_l (ZF.modelsKP hZF) (hv.isSetFunctionFromTo fk.1 (trans E hEΓ))
  have du s x (hsx : Rd_entry_d s x u) := (pred D d.val hDd x).mpr
    ⟨s, ((hu.2 s x).mp hsx).1, ((hu.2 s x).mp hsx).2⟩
  have dv s x (hsx : Rd_entry_d s x v) := (pred E e.val hEe x).mpr
    ⟨s, ((hv.2 s x).mp hsx).1, ((hv.2 s x).mp hsx).2⟩
  have comm s w x y (hsw : Rd_entry_d s w t) (hsx : Rd_entry_d s x v) (hwy : Rd_entry_d w y u) :=
    read s w x y hsw ((hv.2 s x).mp hsx).2 ((hu.2 w y).mp hwy).2
  have push := ec_raw_push_l hZF hω hX mx theory model hj ext d e ⟨p, hp⟩ fp fu fv ft dv comm
    hP hQ inside us vs coherent hm hn hr hb hra haU hbV hD hE ts
  obtain ⟨H, j, hH, spec, embed, lift⟩ := rc_projection_embedding_l hZFC hω hX mx theory collection model hj
    d e ⟨p, hp⟩ μ₀ f₀ μ₁ f₁ small₀ small₁ fp fu fv du dv comm hP hQ hU hV push hG₀ hG₁ model₀ model₁
  have pull f g (hfg : Rd_entry_d f g H) : Ep_pull_d κ Y m n r f g :=
    ep_pull_of_comp_l hD hE ft (model₀.map.functions f (hH.input_mem_of_pairMember hfg)) ts ((spec f g).mp hfg).2.2
  have any B C (hBC : Rd_entry_d B C j) f (hf : M.mem f B) : ∃ g, M.mem g C ∧ Ep_pull_d κ Y m n r f g := by
    have fp := model₀.map.member_l I hZF.1 hU.base (embed.1.1.input_mem_of_pairMember hBC) hf
    obtain ⟨g, hg, hfg⟩ := hH.2.2 f (model₀.map.projection.input_mem_of_pairMember fp)
    obtain ⟨C', _, gp⟩ := model₁.map.projection.2.2 g hg
    have eq := embed.1.1.1.2 B C' C (lift f g B C' hfg fp gp) hBC
    exact ⟨g, eq ▸ model₁.map.representative_l I hV.base gp, pull f g hfg⟩
  obtain ⟨i₀, hi₀, const₀⟩ := rc_constant_embedding_l hZF hω hX mx theory collection model hj
    d μ₀ f₀ small₀ fu du hP hU hG₀ model₀
  obtain ⟨i₁, hi₁, const₁⟩ := rc_constant_embedding_l hZF hω hX mx theory collection model hj
    e μ₁ f₁ small₁ fv dv hQ hV hG₁ model₁
  refine ⟨t, H, j, htΓ, ft, ts, hH, spec, embed, lift, ?_,
    (fun B C hBC f hf => (any B C hBC f hf).elim fun g hg => ⟨m, n, r, g, hm, hn, hr, hb, hra, hg⟩),
    i₀, i₁, hi₀, hi₁, const₀, const₁,
    rs_projection_constant_l I model₀.map model₁.map ft hH (fun f g h => ((spec f g).mp h).2.2)
      embed.1.1 lift hi₁.1.1 const₀ const₁⟩
  intro B C
  constructor
  · intro hBC
    have hB := embed.1.1.input_mem_of_pairMember hBC
    obtain ⟨f, fp⟩ := (model₀.map.range B).mp hB
    have hf := model₀.map.representative_l I hU.base fp
    obtain ⟨g, hg, fg⟩ := any B C hBC f hf
    exact ⟨hB, embed.1.1.output_mem_of_pairMember hBC, m, n, r, f, g, hm, hn, hr, hb, hra, hf, hg, fg⟩
  · rintro ⟨hB, hC, m', n', r', f, g, _, _, hr', hb', hra', hf, hg, fg⟩
    have eqn := hb'.domain_eq_l hZF.1 hb
    subst n'
    have eqm := hra'.1.domain_eq_l hZF.1 hra.1
    subst m'
    have eqr := ec_factor_unique_l hZF.1 inj hr' hr hra' hra
    subst r'
    have fp := model₀.map.member_l I hZF.1 hU.base hB hf
    have gp := model₁.map.member_l I hZF.1 hV.base hC hg
    obtain ⟨g', _, hfg'⟩ := hH.2.2 f (model₀.map.projection.input_mem_of_pairMember fp)
    have eq := ep_pull_unique_l (ZF.modelsKP hZF) hr (pull f g' hfg') fg
    exact lift f g B C (eq ▸ hfg') fp gp

end YesMetaZFC.SetTheory.LargeCardinal
