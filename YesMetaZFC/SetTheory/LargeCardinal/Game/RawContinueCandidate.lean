import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.SetTheory.LargeCardinal.Game.RigidAssemble
import YesMetaZFC.SetTheory.CumulativeRelativeRestriction
import YesMetaZFC.SetTheory.LargeCardinal.Types.ContinueScope
import YesMetaZFC.SetTheory.LargeCardinal.Game.NativePlay
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawPrepareRoot
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyAnchor

/-! # 同一原共同层中的完整候选

dcp 见证是实际低查询域的子集，因而由源秩层的子集闭包回收。
完整共同图将该见证及其全部量词一起搬运，再在目标反射层重读；
两侧始终使用各自原关系，不经过工作模型或重新选择后继。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 目标共同层的配对闭包来自同一满图，不要求另外给出目标极限高度。 -/
theorem Ic_common_d.pair_native_l
    {X R Y S L l U V Γ t c d : M.Domain}
    (h : Ic_common_d I X R Y S L l U V Γ t)
    (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (hX : (smdl_structure_l I (R := R) mx.2.1).Models KP) :
    ∀ a b : (smdl_structure_l I (R := S) my.2.1).Domain,
      Rd_entry_d a.val V S → Rd_entry_d b.val V S →
        ∃ p : (smdl_structure_l I (R := S) my.2.1).Domain,
          Rd_entry_d p.val V S ∧ Pair_d (smdl_structure_l I (R := S) my.2.1) p a b := by
  let N := smdl_structure_l I (R := R) mx.2.1
  let P := smdl_structure_l I (R := S) my.2.1
  let L₀ : N.Domain := ⟨L,h.left_rank.1⟩
  let U₀ : N.Domain := ⟨U,h.left_rank.2.1⟩
  have rank : V_d (kp_pair_l hX) L₀ U₀ := (rr_rank_native_l I mx.2.1 hX L₀ U₀).mp h.left_rank
  have limit : N.IsLimitOrdinal L₀ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mx.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => L₀)).mp h.limit)
  intro a b ha hb
  obtain ⟨x,hx,xa⟩ := (h.image a.val).mp ha
  obtain ⟨y,hy,yb⟩ := (h.image b.val).mp hb
  let x₀ : N.Domain := ⟨x,((h.carrier x).mp hx).1⟩
  let y₀ : N.Domain := ⟨y,((h.carrier y).mp hy).1⟩
  obtain ⟨p,hp,pair⟩ := sc_v_pair_l hX limit rank x₀ y₀
    ((h.carrier x).mp hx).2 ((h.carrier y).mp hy).2
  have hpΓ := (h.carrier p.val).mpr ⟨p.property,hp⟩
  obtain ⟨q,hq,pq⟩ := h.injection.1.2.2 p.val hpΓ
  refine ⟨⟨q,hq⟩,(h.image q).mpr ⟨p.val,hpΓ,pq⟩,fun z => ?_⟩
  change Rd_entry_d z.val q S ↔ z = a ∨ z = b
  constructor
  · intro hz
    obtain ⟨r,hr,rz⟩ := (h.pred p.val q pq z.val).mp hz
    let r₀ : N.Domain := ⟨r,(mx.2.2.2 r p.val hr).1⟩
    rcases (pair r₀).mp hr with eq | eq
    · have eq : r = x := congrArg Subtype.val eq
      subst r
      exact Or.inl (Subtype.ext (h.injection.1.1.2 x z.val a.val rz xa))
    · have eq : r = y := congrArg Subtype.val eq
      subst r
      exact Or.inr (Subtype.ext (h.injection.1.1.2 y z.val b.val rz yb))
  · rintro (rfl | rfl)
    · exact (h.pred p.val q pq z.val).mpr ⟨x,(pair x₀).mpr (Or.inl rfl),xa⟩
    · exact (h.pred p.val q pq z.val).mpr ⟨y,(pair y₀).mpr (Or.inr rfl),yb⟩

/-- 低查询域回收同一次 dcp 见证；全公式经实际共同切片同构传输。 -/
private theorem Ic_common_d.elastic_native_l
    {X R Y S L l U V Γ t c d w η C w' η' C' : M.Domain}
    (h : Ic_common_d I X R Y S L l U V Γ t)
    (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (hX : (smdl_structure_l I (R := R) mx.2.1).Models KP)
    (hY : (smdl_structure_l I (R := S) my.2.1).Models KP)
    (cx : Tg_context_d I w X R η C) (cy : Tg_context_d I w' Y S η' C')
    (inside : ∀ x, Rd_entry_d x V S → Rd_entry_d x C' S)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) mx.2.1).Domain //
      (smdl_structure_l I (R := R) mx.2.1).mem x ⟨C,cx.member⟩})
    (nd : Nonempty {x : (smdl_structure_l I (R := S) my.2.1).Domain //
      (smdl_structure_l I (R := S) my.2.1).mem x ⟨C',cy.member⟩})
    (ρ : Env (rt_model_l (M := smdl_structure_l I (R := R) mx.2.1) ⟨C,cx.member⟩ nc) 12)
    (θ : Env (rt_model_l (M := smdl_structure_l I (R := S) my.2.1) ⟨C',cy.member⟩ nd) 12)
    (points : ∀ i, Rd_entry_d (ρ.bound i).val.val (θ.bound i).val.val t)
    (valid : Formula.satisfies ρ
      (tg_elastic_m (.bound 4) (.bound 1) (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 0))) :
    Formula.satisfies θ
      (tg_elastic_m (.bound 4) (.bound 1) (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 0)) := by
  let N := smdl_structure_l I (R := R) mx.2.1
  let P := smdl_structure_l I (R := S) my.2.1
  let U₀ : N.Domain := ⟨U,h.left_rank.2.1⟩
  let V₀ : P.Domain := ⟨V,h.right_rank.2.1⟩
  let L₀ : N.Domain := ⟨L,h.left_rank.1⟩
  have ru : V_d (kp_pair_l hX) L₀ U₀ := (rr_rank_native_l I mx.2.1 hX L₀ U₀).mp h.left_rank
  have rv : V_d (kp_pair_l hY) (⟨l,h.right_rank.1⟩ : P.Domain) V₀ :=
    (rr_rank_native_l I my.2.1 hY _ V₀).mp h.right_rank
  have limit : N.IsLimitOrdinal L₀ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mx.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => L₀)).mp h.limit)
  have ut := v_transitive_l (kp_pair_l hX) ru
  have vt := v_transitive_l (kp_pair_l hY) rv
  have up := sc_v_pair_l hX limit ru
  have vp := h.pair_native_l hZF mx my hX
  have fs := cx.finite_l mx.2.1 hX.1
  have ft := cy.finite_l my.2.1 hY.1
  have low (i) : N.mem (ρ.bound i).val U₀ :=
    ((h.carrier _).mp (h.injection.1.input_mem_of_pairMember (points i))).2
  have low' (i) : P.mem (θ.bound i).val V₀ := (h.image _).mpr
    ⟨_,h.injection.1.input_mem_of_pairMember (points i),points i⟩
  let nu : Nonempty {x : N.Domain // N.mem x U₀} := ⟨⟨(ρ.bound 0).val,low 0⟩⟩
  let nv : Nonempty {x : P.Domain // P.mem x V₀} := ⟨⟨(θ.bound 0).val,low' 0⟩⟩
  let ρU : Env (rt_model_l U₀ nu) 12 := ⟨fun i => ⟨(ρ.bound i).val,low i⟩,fun _ => ⟨(ρ.bound 0).val,low 0⟩⟩
  let θV : Env (rt_model_l V₀ nv) 12 := ⟨fun i => ⟨(θ.bound i).val,low' i⟩,fun _ => ⟨(θ.bound 0).val,low' 0⟩⟩
  let φ : Formula 1 12 :=
    tg_elastic_m (.bound 4) (.bound 1) (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 0)
  have closed : φ.FreeClosed := by simp -implicitDefEqProofs [φ]
  have source : Formula.satisfies ρU φ := by
    simp only [tg_elastic_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff] at valid
    obtain ⟨v,drop,elastic⟩ := valid
    have drop := (td_dcp_source_l hX.1 (KP.exists_pair hX) fs.transitive nc fs.pair
      (ρ.push v) (.bound 5) (.bound 2) (.bound 8) (.bound 1) (.bound 0)).mp drop
    have elastic := (ee_elastic_absolute_l fs.transitive nc (ρ.push v)
      (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 0)).mp elastic
    have hv : N.mem v.val U₀ := v_subset_mem_l (kp_pair_l hX) ru (low 7)
      (fun p hp => ((drop.2 p).mp hp).1)
    let v₀ : (rt_model_l U₀ nu).Domain := ⟨v.val,hv⟩
    simp only [φ,tg_elastic_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff]
    exact ⟨v₀,(td_dcp_source_l hX.1 (KP.exists_pair hX) ut nu up
      (ρU.push v₀) (.bound 5) (.bound 2) (.bound 8) (.bound 1) (.bound 0)).mpr drop,
      (ee_elastic_absolute_l ut nu (ρU.push v₀)
        (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 0)).mpr elastic⟩
  have target := (rr_native_slice_l I mx.2.1 my.2.1 U₀ V₀ nu nv h.carrier h.injection h.image h.pred
    φ closed ρU θV points).mp source
  simp only [φ,tg_elastic_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff] at target ⊢
  obtain ⟨v,drop,elastic⟩ := target
  have drop := (td_dcp_source_l hY.1 (KP.exists_pair hY) vt nv vp
    (θV.push v) (.bound 5) (.bound 2) (.bound 8) (.bound 1) (.bound 0)).mp drop
  have elastic := (ee_elastic_absolute_l vt nv (θV.push v)
    (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 0)).mp elastic
  let v₀ : (rt_model_l (M := P) ⟨C',cy.member⟩ nd).Domain :=
    ⟨v.val,inside v.val.val v.property⟩
  exact ⟨v₀,(td_dcp_source_l hY.1 (KP.exists_pair hY) ft.transitive nd ft.pair
    (θ.push v₀) (.bound 5) (.bound 2) (.bound 8) (.bound 1) (.bound 0)).mpr drop,
    (ee_elastic_absolute_l ft.transitive nd (θ.push v₀)
      (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 0)).mpr elastic⟩

/-- 十二个候选坐标保留同一共同图，语言与 dcp 均由实际源证书生产。 -/
theorem Ic_common_d.candidate_native_l
    {Ω b B R₀ c X R d Y S j k C₀ w₀ z₀ w z η C w' z' η' C' L l U V Γ t : M.Domain}
    (common : Ic_common_d I X R Y S L l U V Γ t)
    (hΩ : M.IsOmega Ω) (mb : Smdl_d I b B R₀) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (hX : (smdl_structure_l I (R := R) mx.2.1).Models KP)
    (hY : (smdl_structure_l I (R := S) my.2.1).Models KP)
    (left : Smap_d I Ω b c B X j) (right : Smap_d I Ω b d B Y k) (ext : Rf_ext_d I B R₀)
    (root : Rr_layer_d I Ω B R₀ w₀ z₀) (source : Rr_layer_d I Ω X R w z)
    (target : Rr_layer_d I Ω Y S w' z')
    (cx : Tg_context_d I w X R η C) (cy : Tg_context_d I w' Y S η' C')
    (iC : Rd_entry_d C₀ C j) (iD : Rd_entry_d C₀ C' k)
    (inside : ∀ x, Rd_entry_d x V S → Rd_entry_d x C' S)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) mx.2.1).Domain //
      (smdl_structure_l I (R := R) mx.2.1).mem x ⟨C,cx.member⟩})
    (ρ : Env (rt_model_l (M := smdl_structure_l I (R := R) mx.2.1) ⟨C,cx.member⟩ nc) 12)
    (hw : (ρ.bound 2).val.val = w) (hk : Rd_entry_d (ρ.bound 3).val.val U R)
    (hu : Rd_entry_d (ρ.bound 0).val.val U R) (valid : Formula.satisfies ρ tg_candidate0_m) :
    ∃ nd : Nonempty {x : (smdl_structure_l I (R := S) my.2.1).Domain //
      (smdl_structure_l I (R := S) my.2.1).mem x ⟨C',cy.member⟩},
    ∃ θ : Env (rt_model_l (M := smdl_structure_l I (R := S) my.2.1) ⟨C',cy.member⟩ nd) 12,
      (∀ i, Rd_entry_d (ρ.bound i).val.val (θ.bound i).val.val t) ∧
      (θ.bound 2).val.val = w' ∧ Formula.satisfies θ tg_candidate0_m := by
  let N := smdl_structure_l I (R := R) mx.2.1
  let P := smdl_structure_l I (R := S) my.2.1
  let U₀ : N.Domain := ⟨U,common.left_rank.2.1⟩
  let w₀ : N.Domain := ⟨w,source.member⟩
  obtain ⟨language,elastic⟩ := (Formula.satisfies_conj_iff ..).mp valid
  let ε := Env.reindex ρ (fun i : Fin 10 => i.succ.succ)
  have language : Formula.satisfies ε ee_language0_m := (Formula.satisfies_rename ..).mp language
  obtain ⟨hn,low,nd,χ,images,hχ,moved⟩ := common.language_native_l hZF hΩ mb mx my hX hY
    left right ext root source target cx cy iC iD inside nc ε hw hk language
  have fs := cx.finite_l mx.2.1 hX.1
  have omega : N.IsOmega w₀ := source.omega_l I (ZF.modelsKP hZF) hΩ hX.1
  have ru : V_d (kp_pair_l hX) (⟨L,common.left_rank.1⟩ : N.Domain) U₀ :=
    (rr_rank_native_l I mx.2.1 hX _ U₀).mp common.left_rank
  have ut := v_transitive_l (kp_pair_l hX) ru
  have hw₀ : (ρ.bound 2).val = w₀ := Subtype.ext hw
  have hwU : N.mem w₀ U₀ := Eq.mp (congrArg (fun a : N.Domain => N.mem a U₀) hw₀) (low 0)
  have drop := elastic
  simp only [tg_elastic_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff] at drop
  obtain ⟨v,dcp,_⟩ := drop
  have dcp := (td_dcp_source_l hX.1 (KP.exists_pair hX) fs.transitive nc fs.pair
    (ρ.push v) (.bound 5) (.bound 2) (.bound 8) (.bound 1) (.bound 0)).mp dcp
  obtain ⟨m,sm,hm⟩ := omega.1.2 (ρ.bound 4).val hn
  have eqm : m = (ρ.bound 1).val := hX.1.eq_of_same_members m (ρ.bound 1).val
    (fun a => (sm a).trans (dcp.1 a).symm)
  have hmU : N.mem (ρ.bound 1).val U₀ := ut w₀ hwU _ (eqm ▸ hm)
  have values (a : N.Domain) (ha : N.mem a U₀) :
      ∃ b : (rt_model_l (M := P) ⟨C',cy.member⟩ nd).Domain, Rd_entry_d a.val b.val.val t := by
    have haΓ := (common.carrier a.val).mpr ⟨a.property,ha⟩
    obtain ⟨b,hb,ab⟩ := common.injection.1.2.2 a.val haΓ
    exact ⟨⟨⟨b,hb⟩,inside b ((common.image b).mpr ⟨a.val,haΓ,ab⟩)⟩,ab⟩
  obtain ⟨u',iu⟩ := values (ρ.bound 0).val hu
  obtain ⟨m',im⟩ := values (ρ.bound 1).val hmU
  let θ := χ.push m' |>.push u'
  have points : ∀ i, Rd_entry_d (ρ.bound i).val.val (θ.bound i).val.val t :=
    Fin.cases iu (Fin.cases im images)
  have lang : Formula.satisfies θ (ee_language0_m.rename (fun i => i.succ.succ)) :=
    (Formula.satisfies_rename ..).mpr ((Formula.closed_env_l ee_language0_m ee_language0_closed_l
      (show χ.bound = (Env.reindex θ (fun i : Fin 10 => i.succ.succ)).bound from rfl)).mp moved)
  exact ⟨nd,θ,points,hχ,(Formula.satisfies_conj_iff ..).mpr
    ⟨lang,common.elastic_native_l hZF mx my hX hY cx cy inside nc nd ρ θ points elastic⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原模型中的秩比较给出实际最大序数查询

当前候选与继续输入共享 τ，故其常量域相同。固定低层位于旧 κ 以下，而
真实超过关系给出 κ<τ；于是三个低层参数进入候选常量域，刚性核可直接调用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tg_rigid_native_l {ω η C γ Z : M.Domain}
    (rankC : V_d I η C) (fs : Fs_read_d ω C) (nc : Nonempty {x // M.mem x C})
    (kernel : Tg_kernel_d (rt_model_l C nc))
    (ρ : Env (rt_model_l C nc) 29) (χ ψ : Env (rt_model_l C nc) 12) (ε : Env (rt_model_l C nc) 7)
    (rankZ : V_d I γ Z) (lower : M.MemberSubset γ (ρ.bound 1).val)
    (low : M.mem (ψ.bound 4).val Z ∧ M.mem (ψ.bound 5).val Z ∧ M.mem (ψ.bound 6).val Z)
    (ωχ : χ.bound 2 = ρ.bound 0) (τχ : χ.bound 3 = ρ.bound 8)
    (uχ : χ.bound 0 = ρ.bound 13) (mχ : χ.bound 1 = ρ.bound 9)
    (ωψ : ψ.bound 0 = ρ.bound 0) (lψ : ψ.bound 2 = χ.bound 4)
    (nψ : ψ.bound 3 = ρ.bound 9) (eψ : ψ.bound 1 = ε.bound 1)
    (ωε : ε.bound 0 = ρ.bound 0) (nε : ε.bound 3 = ρ.bound 3)
    (hi : M.mem (ε.bound 2).val (ρ.bound 3).val) (hh : M.mem (ε.bound 6).val (ρ.bound 7).val)
    (seed : Formula.satisfies ρ tc_seed0_m) (candidate : Formula.satisfies χ tg_candidate0_m)
    (queries : Formula.satisfies ψ tg_query_row0_m) (reply : Formula.satisfies ε tg_reply_base0_m) :
    (M.mem (ψ.bound 4).val (χ.bound 6).val ∧ M.mem (ψ.bound 5).val (χ.bound 6).val ∧
      M.mem (ψ.bound 6).val (χ.bound 6).val) ∧ M.mem (ψ.bound 8).val (ρ.bound 13).val := by
  have data := seed
  simp only [tc_seed0_m, Formula.satisfies_conj_iff] at data
  obtain ⟨_, _, _, _, _, oldRank, oldConstants, _, exceeds, _⟩ := data
  have language := ((Formula.satisfies_conj_iff ..).mp candidate).1
  simp only [Formula.satisfies_rename, ee_language0_m, Formula.satisfies_conj_iff] at language
  obtain ⟨_, limit, newRank, constants, _⟩ := language
  have rank₀ := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc ρ (.bound 8) (.bound 10)).mp oldRank
  have rank₁ := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc χ (.bound 3) (.bound 5)).mp newRank
  have eqτ := congrArg Subtype.val τχ
  have eqB := rank₀.unique_l hZF fs.transitive (ρ.bound 10).property (χ.bound 5).property
    (Eq.mp (congrArg (fun a => Vr_d C a (χ.bound 5).val) eqτ) rank₁)
  have cons₀ := (rt_model_delta_l fs.transitive nc (tt_constants0_delta_l ..) ρ).mp oldConstants
  have cons₁ := (rt_model_delta_l fs.transitive nc (tt_constants0_delta_l (.bound 1) (.bound 3) (.bound 4))
    (χ.reindex (fun i : Fin 10 => i.succ.succ))).mp constants
  simp only [tt_constants0_sat_l hZF.1, @eval_image_env_l (rt_model_l C nc) M Subtype.val] at cons₀ cons₁
  have eqV : χ.bound 6 = ρ.bound 11 := Subtype.ext (hZF.1.eq_of_same_members _ _ (fun a =>
    (cons₁ a).trans ((or_congr (Iff.of_eq (congrArg (fun B => M.mem a B) eqB.symm))
      (Iff.of_eq (congrArg (fun τ => a = τ) eqτ))).trans (cons₀ a).symm)))
  -- 先把反射层内的 Vτ 识别为原模型中的实际 Vτ，再作原生秩比较。
  have hτ := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) _).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp limit)
  have hτη := ZF.v_ordinal_height_l hZF rankC hτ.1 (χ.bound 3).property
  obtain ⟨B, rB⟩ := ZF.v_exists_l I hZF hτ.1
  have hBC := ZF.v_mem_l I hZF rB rankC hτη
  have eq := vr_agree_l hZF fs.transitive (χ.bound 5).property rB (fs.transitive B hBC) rank₁
  have full : V_d I (χ.bound 3).val (χ.bound 5).val := by rw [eq]; exact rB
  have hκτ : M.mem (ρ.bound 1).val (χ.bound 3).val :=
    eqτ.symm ▸ ((Formula.satisfies_conj_iff ..).mp exceeds).1
  have sub := ZF.v_mono_l I hZF rankZ full
    (fun a ha => hτ.1.transitive (ρ.bound 1).val hκτ a (lower a ha))
  have member a (ha : M.mem a Z) := (cons₁ a).mpr (Or.inl (sub a ha))
  have scope : M.mem (ψ.bound 4).val (χ.bound 6).val ∧ M.mem (ψ.bound 5).val (χ.bound 6).val ∧
      M.mem (ψ.bound 6).val (χ.bound 6).val := ⟨member _ low.1, member _ low.2.1, member _ low.2.2⟩
  exact ⟨scope, tg_rigid_assemble_l kernel ρ χ ψ ε ωχ τχ uχ mχ ωψ lψ nψ eψ ωε nε hi hh eqV
    scope seed candidate queries reply⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 第一次原后继中的实际候选与根查询

继续核和当前 issued 产生完整候选及查询行。候选沿同一次共同图搬运；
根查询沿该图的真实逆图应用根切片回读，因而得到同一正向图上的像。
节点、最大序数查询及恢复所需的低参数都从这些实际证书读取。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_common_d.continue_candidate_l
    {Ω c₀ X₀ R₀ w₀ wcut z₀ C₀ γ₀ D₀ B₀ A₀ A c N R w z η C p d P S w' z' η' C' q
      L l U V Γ g γ Vγ t γ' Vγ' t' : M.Domain}
    (common : Ic_common_d I N R P S L l U V Γ g)
    (hΩ : M.IsOmega Ω) (root : Zc_model_d I Ω c₀ X₀ R₀)
    (mn : Smdl_d I c N R) (mp : Smdl_d I d P S)
    (left : Smap_d I Ω c₀ c X₀ N p) (right : Smap_d I Ω c₀ d X₀ P q)
    (rootNumbers : Rr_layer_d I Ω X₀ R₀ w₀ z₀)
    (numbers : Rr_layer_d I Ω N R w z) (targetNumbers : Rr_layer_d I Ω P S w' z')
    (context : Tg_context_d I w N R η C) (target : Tg_context_d I w' P S η' C')
    (cut : Tg_root_cut_d I c₀ X₀ R₀ wcut γ₀ B₀ A₀ D₀ A)
    (sourceSlice : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ N R C p γ Vγ t)
    (targetSlice : Tg_root_slice_d I X₀ R₀ γ₀ D₀ C₀ P S C' q γ' Vγ' t')
    (roots : Tg_root_square_d D₀ p q g)
    (inside : ∀ x, Rd_entry_d x V S → Rd_entry_d x C' S)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) mn.2.1).Domain //
      (smdl_structure_l I (R := R) mn.2.1).mem x ⟨C,context.member⟩})
    (nd : Nonempty {x : (smdl_structure_l I (R := S) mp.2.1).Domain //
      (smdl_structure_l I (R := S) mp.2.1).mem x ⟨C',target.member⟩})
    (ρ : Env (rt_model_l (M := smdl_structure_l I (R := R) mn.2.1) ⟨C,context.member⟩ nc) 29)
    (ι : Env (rt_model_l (M := smdl_structure_l I (R := R) mn.2.1) ⟨C,context.member⟩ nc) 46)
    (ε₀ : Env (rt_model_l (M := smdl_structure_l I (R := R) mn.2.1) ⟨C,context.member⟩ nc) 7)
    (seed : Formula.satisfies ρ tc_seed0_m) (issued : Formula.satisfies ι tg_issued0_m)
    (hw : (ρ.bound 0).val.val = w)
    (links : ∀ i : Fin 4, ρ.bound ([0,8,9,13].get i) = ι.bound ([0,24,28,25].get i))
    (high : Rd_entry_d (ρ.bound 8).val.val L R)
    (omegaSlice : Rd_entry_d w Vγ R) (alphabet : Rd_entry_d A₀ (ι.bound 6).val.val p)
    (lower : ∀ x, Rd_entry_d x γ R → Rd_entry_d x (ρ.bound 1).val.val R)
    (reply : Formula.satisfies ε₀ tg_reply_base0_m)
    (ωε : ε₀.bound 0 = ρ.bound 0) (nε : ε₀.bound 3 = ρ.bound 3)
    (hi : (smdl_structure_l I (R := R) mn.2.1).mem (ε₀.bound 2).val (ρ.bound 3).val)
    (hh : (smdl_structure_l I (R := R) mn.2.1).mem (ε₀.bound 6).val (ρ.bound 7).val)
    (empty : ∀ x : (smdl_structure_l I (R := R) mn.2.1).Domain,
      ¬ (smdl_structure_l I (R := R) mn.2.1).mem x (ε₀.bound 1).val) :
    ∃ ψ : Env (rt_model_l (M := smdl_structure_l I (R := R) mn.2.1) ⟨C,context.member⟩ nc) 12,
    ∃ ε ζ : Env (rt_model_l (M := smdl_structure_l I (R := S) mp.2.1) ⟨C',target.member⟩ nd) 12,
      Formula.satisfies ψ tg_query_row0_m ∧
      (∀ i : Fin 6, ψ.bound ([0,1,2,3,4,6].get i) = ι.bound ([0,1,27,28,26,23].get i)) ∧
      Tg_play_d I N R C (ι.bound 4).val.val (ι.bound 3).val.val (ι.bound 20).val.val (ψ.bound 5).val.val ∧
      Rd_entry_d (ψ.bound 5).val.val Vγ R ∧ Rd_entry_d (ψ.bound 6).val.val Vγ R ∧
      Formula.satisfies ε tg_candidate0_m ∧ Formula.satisfies ζ tg_query_row0_m ∧
      (∀ i : Fin 12, Rd_entry_d (ι.bound ([25,28,0,24,27,29,30,31,32,33,34,35].get i)).val.val
        (ε.bound i).val.val g) ∧
      (∀ i, Rd_entry_d (ψ.bound i).val.val (ζ.bound i).val.val g) ∧
      (ε.bound 2).val.val = w' ∧ (ζ.bound 0).val.val = w' ∧
      Rd_entry_d (ε.bound 1).val.val w' S ∧
      Rd_entry_d (ζ.bound 11).val.val (ε.bound 0).val.val S ∧
      Rd_entry_d (ζ.bound 8).val.val (ε.bound 0).val.val S ∧
      (Rd_entry_d (ζ.bound 4).val.val (ε.bound 6).val.val S ∧
        Rd_entry_d (ζ.bound 5).val.val (ε.bound 6).val.val S ∧
        Rd_entry_d (ζ.bound 6).val.val (ε.bound 6).val.val S) ∧
      ∀ x : (smdl_structure_l I (R := S) mp.2.1).Domain,
        ¬ (smdl_structure_l I (R := S) mp.2.1).mem x (ζ.bound 1).val := by
  let Nn := smdl_structure_l I (R := R) mn.2.1
  let Pn := smdl_structure_l I (R := S) mp.2.1
  have ground := ZFC.models_zf_l ((root.map_l hZF hΩ mn left).native_l I hZF hΩ)
  have targetZF := ZFC.models_zf_l ((root.map_l hZF hΩ mp right).native_l I hZF hΩ)
  have hN := ZF.modelsKP ground
  have hP := ZF.modelsKP targetZF
  let wn : Nn.Domain := ⟨w,context.omega_mem⟩
  let Un : Nn.Domain := ⟨U,common.left_rank.2.1⟩
  let Ln : Nn.Domain := ⟨L,common.left_rank.1⟩
  let aq : Nn.Domain := ⟨γ,sourceSlice.rank.1⟩
  let Vq : Nn.Domain := ⟨Vγ,sourceSlice.rank.2.1⟩
  have fs := context.finite_l mn.2.1 hN.1
  have fs' := target.finite_l mp.2.1 hP.1
  have omega := numbers.omega_l I (ZF.modelsKP hZF) hΩ hN.1
  have rankC := (rr_rank_native_l I mn.2.1 hN ⟨η,context.height⟩ ⟨C,context.member⟩).mp
    ((rr_rank_truth_l I).mpr context.rank)
  have rankU := (rr_rank_native_l I mn.2.1 hN Ln Un).mp common.left_rank
  have limit : Nn.IsLimitOrdinal Ln := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => Ln)).mp common.limit)
  have tau : Nn.mem (ρ.bound 8).val Un := KP.v_ordinal_subset_l hN rankU _ high
  have hwN : (ρ.bound 0).val = wn := Subtype.ext hw
  obtain ⟨finiteCurrent,_,_,typeLow⟩ := tc_current_scope_l ground omega rankC fs nc ρ hwN rankU limit tau seed
  have rankG := (rr_rank_native_l I mn.2.1 hN aq Vq).mp sourceSlice.rank
  have limitG : Nn.IsLimitOrdinal aq := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => aq)).mp sourceSlice.limit)
  have wi : (ι.bound 0).val = wn := (congrArg Subtype.val (links 0)).symm.trans hwN
  have aD := (cut.carrier A₀).mpr ⟨(cut.model.2.2.2 A₀ B₀ cut.alphabet).1,cut.alphabet⟩
  obtain ⟨a,_,ia⟩ := sourceSlice.injection.1.2.2 A₀ aD
  have ea := left.1.1.1.2 A₀ a (ι.bound 6).val.val (sourceSlice.root A₀ a ia) alphabet
  have letters : Rd_entry_d (ι.bound 6).val.val Vγ R :=
    ea ▸ (sourceSlice.image a).mpr ⟨A₀,aD,ia⟩
  obtain ⟨ψ,χ,queries,coords,node,low,play,valid,same⟩ :=
    tg_issued_query_scope_l hN omega fs nc ι rankG limitG wi omegaSlice letters issued
  have chi0 : (χ.bound 0).val = (ρ.bound 13).val := congrArg Subtype.val ((same 0).trans (links 3).symm)
  have chi3 : (χ.bound 3).val = (ρ.bound 8).val := congrArg Subtype.val ((same 3).trans (links 1).symm)
  have chiw : (χ.bound 2).val.val = w := congrArg Subtype.val
    ((congrArg Subtype.val ((same 2).trans (links 0).symm)).trans hwN)
  have state := (tg_issued_sat_l (rt_pair_l fs.transitive nc ground.1 fs.pair)
    (rt_model_ext_l ground.1 fs.transitive nc) ι).mp issued
  have control := state.control
  simp only [tg_control0_m,Formula.satisfies_conj_iff] at control
  have rules := control.2.2.1
  simp only [tg_rules_m,Formula.satisfies_conj_iff,Formula.satisfies_isEmpty_iff] at rules
  have he : ∀ x : Nn.Domain, ¬ Nn.mem x (ι.bound 1).val := fun x hx =>
    rules.2.1 ⟨x,fs.transitive _ (ι.bound 1).property x hx⟩ hx
  have eqe : ι.bound 1 = ε₀.bound 1 := Subtype.ext (ground.1.eq_of_same_members _ _
    (fun x => ⟨fun hx => (he x hx).elim,fun hx => (empty x hx).elim⟩))
  obtain ⟨scope,max⟩ := tg_rigid_native_l ground rankC fs nc (context.kernel_l mn.2.1 nc)
    ρ χ ψ ε₀ rankG (fun x hx => lower x.val hx) ⟨low 4,low 5,low 6⟩
    ((same 2).trans (links 0).symm) ((same 3).trans (links 1).symm)
    ((same 0).trans (links 3).symm) ((same 1).trans (links 2).symm)
    ((coords 0).trans (links 0).symm) ((coords 2).trans (same 4).symm)
    ((coords 3).trans (links 2).symm) ((coords 1).trans eqe)
    ωε nε hi hh seed valid queries reply
  have qm : Nn.mem (ψ.bound 8).val (ι.bound 25).val :=
    Eq.mp (congrArg (fun a => Nn.mem (ψ.bound 8).val a) (congrArg Subtype.val (links 3))) max
  obtain ⟨_,ε,points,ew,truth⟩ := common.candidate_native_l hZF hΩ root.model mn mp hN hP left right root.ext
    rootNumbers numbers targetNumbers context target sourceSlice.context targetSlice.context inside nc χ chiw
    (chi3.symm ▸ tau) (chi0.symm ▸ typeLow) valid
  have images i : Rd_entry_d (ι.bound ([25,28,0,24,27,29,30,31,32,33,34,35].get i)).val.val
      (ε.bound i).val.val g := congrArg (fun x => x.val.val) (same i) ▸ points i
  -- 反转同一共同图，再反向使用已经证明的完整根查询回读。
  obtain ⟨_,back,_,_,_,_,inverse⟩ := common.reverse_native_l hZF mn hN
  have inverseSquare := sourceSlice.inverse_square_l I hZF.1 roots common.injection inverse
  obtain ⟨ζ,backPoints,queryTruth⟩ := targetSlice.back_l hZF sourceSlice inverseSquare hΩ root.model mp mn
    right left fs'.transitive fs.transitive nd nc tg_query_row0_m tg_query_row0_closed_l ψ low queries
  have queryImages i : Rd_entry_d (ψ.bound i).val.val (ζ.bound i).val.val g :=
    (inverse _ _).mp (backPoints i)
  have qw : (ζ.bound 0).val.val = w' :=
    (common.injection.1.1.2 _ _ _ (congrArg (fun x => x.val.val) (coords 0) ▸ queryImages 0) (images 2)).trans ew
  have qnode : Rd_entry_d (ζ.bound 11).val.val (ε.bound 0).val.val S :=
    (common.pred _ _ (images 0) _).mpr ⟨_,node,queryImages 11⟩
  have qmax : Rd_entry_d (ζ.bound 8).val.val (ε.bound 0).val.val S :=
    (common.pred _ _ (images 0) _).mpr ⟨_,qm,queryImages 8⟩
  have finite : Nn.mem (ι.bound 28).val (ι.bound 0).val := by
    have em : (ρ.bound 9).val = (ι.bound 28).val := congrArg Subtype.val (links 2)
    have hm : Nn.mem (ι.bound 28).val wn := Eq.mp (congrArg (fun x => Nn.mem x wn) em) finiteCurrent
    exact Eq.mp (congrArg (fun x => Nn.mem (ι.bound 28).val x) wi.symm) hm
  have targetFinite : Rd_entry_d (ε.bound 1).val.val w' S :=
    Eq.mp (congrArg (fun a => Rd_entry_d (ε.bound 1).val.val a S) ew)
      ((common.pred _ _ (images 2) _).mpr ⟨_,finite,images 1⟩)
  have carry i (h : Nn.mem (ψ.bound i).val (χ.bound 6).val) :
      Rd_entry_d (ζ.bound i).val.val (ε.bound 6).val.val S :=
    (common.pred _ _ (images 6) _).mpr ⟨_,
      Eq.mp (congrArg (fun a => Nn.mem (ψ.bound i).val a) (congrArg Subtype.val (same 6))) h,queryImages i⟩
  have emptyQuery : ∀ x : Pn.Domain, ¬ Pn.mem x (ζ.bound 1).val := by
    intro x hx
    obtain ⟨y,hy,iy⟩ := (common.pred _ _ (queryImages 1) x.val).mp hx
    let yn : Nn.Domain := ⟨y,((common.carrier y).mp (common.injection.1.input_mem_of_pairMember iy)).1⟩
    exact he yn (Eq.mp (congrArg (fun a => Nn.mem yn a) (congrArg Subtype.val (coords 1))) hy)
  have play₀ : Tg_play_d I N R C (ι.bound 4).val.val (ι.bound 3).val.val (ι.bound 20).val.val (ψ.bound 5).val.val :=
    (tg_play_native_l I mn.2.1 ground.1 ⟨C,context.member⟩ fs.transitive nc
      (rt_pair_l fs.transitive nc ground.1 fs.pair) (ι.bound 4) (ι.bound 3) (ι.bound 20) (ψ.bound 5)).mpr play
  exact ⟨ψ,ε,ζ,queries,coords,play₀,low 5,low 6,truth,queryTruth,images,queryImages,ew,qw,targetFinite,qnode,qmax,
    ⟨carry 4 scope.1,carry 5 scope.2.1,carry 6 scope.2.2⟩,emptyQuery⟩

end YesMetaZFC.SetTheory.LargeCardinal
