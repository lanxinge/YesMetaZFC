import YesMetaZFC.SetTheory.LargeCardinal.Types.ElasticNumericTransfer
import YesMetaZFC.SetTheory.CumulativeRelativeRead
import YesMetaZFC.SetTheory.CumulativeOrdinalHeight
import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.SetTheory.LargeCardinal.Game.RawContinueCandidate

/-! # 原生模型之间的旧查询运输

完整数值程序经共同根传输。四张查询列在共同秩段内反射，经完整前驱图
搬运后回到目标原生模型；非数值常量始终使用原来的共同图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_common_d.numeric_model_l
    {Ω b B R₀ c X R d Y S j k w₀ z₀ w z w' z' L l U V Γ t : M.Domain}
    (common : Ic_common_d I X R Y S L l U V Γ t)
    (hΩ : M.IsOmega Ω) (mb : Smdl_d I b B R₀) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (hX : (smdl_structure_l I (R := R) mx.2.1).Models KP)
    (hY : (smdl_structure_l I (R := S) my.2.1).Models KP)
    (left : Smap_d I Ω b c B X j) (right : Smap_d I Ω b d B Y k) (eb : Rf_ext_d I B R₀)
    (root : Rr_layer_d I Ω B R₀ w₀ z₀) (source : Rr_layer_d I Ω X R w z)
    (target : Rr_layer_d I Ω Y S w' z')
    (ρ : Env (smdl_structure_l I (R := R) mx.2.1) 8)
    (η : Env (smdl_structure_l I (R := S) my.2.1) 8)
    (points : ∀ i, Rd_entry_d (ρ.bound i).val (η.bound i).val t)
    (hw : (ρ.bound 0).val = w)
    (A : (smdl_structure_l I (R := R) mx.2.1).Domain)
    (hA : Rd_entry_d A.val U R) (names : Tn_names_d (ρ.bound 2) (ρ.bound 3) A)
    (valid : Formula.satisfies ρ ee_numeric0_m) : Formula.satisfies η ee_numeric0_m := by
  let Xn := smdl_structure_l I (R := R) mx.2.1
  let Yn := smdl_structure_l I (R := S) my.2.1
  let Un : Xn.Domain := ⟨U,common.left_rank.2.1⟩
  let Vn : Yn.Domain := ⟨V,common.right_rank.2.1⟩
  let wn : Xn.Domain := ⟨w,source.member⟩
  let wn' : Yn.Domain := ⟨w',target.member⟩
  have hω : ρ.bound 0 = wn := Subtype.ext hw
  have ru := (rr_rank_native_l I mx.2.1 hX (⟨L,common.left_rank.1⟩ : Xn.Domain) Un).mp common.left_rank
  have rv := (rr_rank_native_l I my.2.1 hY (⟨l,common.right_rank.1⟩ : Yn.Domain) Vn).mp common.right_rank
  have ut := v_transitive_l (kp_pair_l hX) ru
  have vt := v_transitive_l (kp_pair_l hY) rv
  have low i : Xn.mem (ρ.bound i) Un :=
    ((common.carrier _).mp (common.injection.1.input_mem_of_pairMember (points i))).2
  have hwU : Xn.mem wn Un := hω ▸ low 0
  have ex := left.extensional_l hZF hΩ mb mx eb
  have ey := right.extensional_l hZF hΩ mb my eb
  have digits := common.layer_image_l (ZF.modelsKP hZF) mx.2.1 ey source target ut hwU
  have hwV : Yn.mem wn' Vn := (common.image w').mpr
    ⟨w,(common.carrier w).mpr ⟨source.member,hwU⟩,digits.1⟩
  have omega := source.omega_l I (ZF.modelsKP hZF) hΩ hX.1
  let nu : Nonempty {x : Xn.Domain // Xn.mem x Un} := ⟨⟨wn,hwU⟩⟩
  let nv : Nonempty {y : Yn.Domain // Yn.mem y Vn} := ⟨⟨wn',hwV⟩⟩
  simp only [ee_numeric0_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff] at valid
  obtain ⟨l₀,v,d₀,e,zg,zh,zi,ze,kw,pg,cg,ph,ch,pi,pair,ci,pe,ce⟩ := valid
  let ε := ρ.push l₀ |>.push v |>.push d₀ |>.push e |>.push zg |>.push zh |>.push zi |>.push ze |>.push kw
  have metaG := pg
  simp only [ee_largest_program_m,Formula.satisfies_bind,ee_largest_program0_m,
    Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at metaG
  have hg : Xn.mem zg wn := hω ▸ metaG.1
  have metaI := pi
  simp only [ee_inacc_program_m,Formula.satisfies_bind,ee_inacc_program0_m,
    Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at metaI
  have hi : Xn.mem zi wn := hω ▸ metaI.1
  have metaH := ph
  simp only [tg_guard_program_m,Formula.satisfies_bind,tg_guard_program0_m,
    Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at metaH
  have hl : Xn.mem l₀ wn := hω ▸ metaH.1
  have hh : Xn.mem zh wn := hω ▸ metaH.2.1
  have metaE := pe
  simp only [ee_stretch_program_m,Formula.satisfies_bind,ee_stretch_program0_m,
    Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at metaE
  obtain ⟨hn,hv,hd,he,hz,_⟩ := metaE
  have hn : Xn.mem (ρ.bound 2) wn := hω ▸ hn
  have hv : Xn.mem v wn := hω ▸ hv
  have hd : Xn.mem d₀ wn := hω ▸ hd
  have he : Xn.mem e wn := hω ▸ he
  have hz : Xn.mem ze wn := hω ▸ hz
  have cg₀ := (tt_code0_sat_l hX ε (.bound 11) (.bound 12) (.bound 4) (.bound 13)).mp cg
  have ch₀ := (tg_guard_code_sat_l hX ε (.bound 11) (.bound 10) (.bound 12) (.bound 8) (.bound 3) (.bound 14)).mp ch
  have ci₀ := (tt_code2_sat_l hX ε (.bound 11) (.bound 12) (.bound 2) (.bound 15) (.bound 11) (.bound 0)).mp ci
  have ce₀ := (ee_stretch_code_sat_l hX.1 ε (.bound 9) (.bound 11) (.bound 10) (.bound 7)
    (.bound 6) (.bound 5) (.bound 1) (.bound 16)).mp ce
  have hkw : Xn.mem kw Un := by
    obtain ⟨_,F,_,_,_,_,cp,slots⟩ := ci₀
    have hF := (cp.mem_l Xn ut (low 6)).2
    obtain ⟨i,ni⟩ := num_exists_l hX 1
    exact (rd_entry_transitive_l ut hF (slots 1 i ni)).2
  have all : ∀ i, Xn.mem (ε.bound i) Un :=
    Fin.cases hkw (Fin.cases (ut wn hwU _ hz) (Fin.cases (ut wn hwU _ hi)
      (Fin.cases (ut wn hwU _ hh) (Fin.cases (ut wn hwU _ hg) (Fin.cases (ut wn hwU _ he)
        (Fin.cases (ut wn hwU _ hd) (Fin.cases (ut wn hwU _ hv) (Fin.cases (ut wn hwU _ hl) low))))))))
  let εU : Env (rt_model_l Un nu) 17 := ⟨fun i => ⟨ε.bound i,all i⟩,fun _ => ⟨wn,hwU⟩⟩
  have values (i : Fin 9) : ∃ y : Yn.Domain, Rd_entry_d (ε.bound (i.castAdd 8)).val y.val t := by
    obtain ⟨y,hy,xy⟩ := common.injection.1.2.2 (ε.bound (i.castAdd 8)).val
      ((common.carrier _).mpr ⟨(ε.bound _).property,all _⟩)
    exact ⟨⟨y,hy⟩,xy⟩
  obtain ⟨v',images⟩ := Classical.axiomOfChoice values
  let υ := η.push (v' 8) |>.push (v' 7) |>.push (v' 6) |>.push (v' 5) |>.push (v' 4)
    |>.push (v' 3) |>.push (v' 2) |>.push (v' 1) |>.push (v' 0)
  have linked : ∀ i, Rd_entry_d (ε.bound i).val (υ.bound i).val t :=
    Fin.cases (images 0) (Fin.cases (images 1) (Fin.cases (images 2) (Fin.cases (images 3)
      (Fin.cases (images 4) (Fin.cases (images 5) (Fin.cases (images 6)
        (Fin.cases (images 7) (Fin.cases (images 8) points))))))))
  have targetLow i : Yn.mem (υ.bound i) Vn := (common.image _).mpr
    ⟨_,common.injection.1.input_mem_of_pairMember (linked i),linked i⟩
  let υV : Env (rt_model_l Vn nv) 17 := ⟨fun i => ⟨υ.bound i,targetLow i⟩,fun _ => ⟨wn',hwV⟩⟩
  have column (φ : Formula 1 17) (closed : φ.FreeClosed) :
      Formula.satisfies εU φ → Formula.satisfies υV φ :=
    (rr_native_slice_l I mx.2.1 my.2.1 Un Vn nu nv common.carrier common.injection common.image
      common.pred φ closed εU υV linked).mp
  have move {n} (φ : Formula 1 n) (closed : φ.FreeClosed) (ix : Fin n → Fin 17)
      (f : Fin n → Term 17) (coords : ∀ i, f i = .bound (ix i))
      (low : ∀ i, ε.bound (ix i) = wn ∨ Xn.mem (ε.bound (ix i)) wn)
      (truth : Formula.satisfies ε (φ.bind f)) : Formula.satisfies υ (φ.bind f) := by
    have eqρ : (Definitional.Env.substitute ε f).bound = (ε.reindex ix).bound := by
      funext i
      change (f i).eval ε = ε.bound (ix i)
      rw [coords i]
      rfl
    have eqυ : (Definitional.Env.substitute υ f).bound = (υ.reindex ix).bound := by
      funext i
      change (f i).eval υ = υ.bound (ix i)
      rw [coords i]
      rfl
    have truth := (Formula.closed_env_l φ closed eqρ).mp ((Formula.satisfies_bind ε f φ).mp truth)
    have moved := (smap_numeric_model_peer_l hZF hΩ mb mx my left right eb ex ey root source target
      φ closed (ε.reindex ix) (υ.reindex ix) (fun i => by
        rcases low i with eq | hi
        · have eq₀ := congrArg Subtype.val eq
          have point : Rd_entry_d w (υ.bound (ix i)).val t :=
            Eq.mp (congrArg (fun x => Rd_entry_d x (υ.bound (ix i)).val t) eq₀) (linked (ix i))
          exact Or.inl ⟨eq₀,common.injection.1.1.2 w _ w' point digits.1⟩
        · obtain ⟨a,_,ha⟩ := (source.image _).mp hi
          exact Or.inr ⟨a,ha,(digits.2 a _).mpr ⟨_,ha,linked (ix i)⟩⟩)).mp truth
    exact (Formula.satisfies_bind υ f φ).mpr ((Formula.closed_env_l φ closed eqυ).mpr moved)
  simp only [ee_numeric0_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff]
  refine ⟨v' 8,v' 7,v' 6,v' 5,v' 4,v' 3,v' 2,v' 1,v' 0,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · let ix : Fin 2 → Fin 17 := Fin.cases 9 (fun _ => 4)
    let f : Fin 2 → Term 17 := Fin.cases (.bound 9) (fun _ => .bound 4)
    exact move ee_largest_program0_m ee_largest_program0_closed_l ix f
      (Fin.cases rfl (fun _ => rfl)) (Fin.cases (Or.inl hω) (fun _ => Or.inr hg)) pg
  · have q := column _ (by simp -implicitDefEqProofs)
      (tt_code0_reflect_l hX ut nu omega hwU εU (.bound 11) (.bound 12) (.bound 4) (.bound 13) hA names cg₀)
    exact (tt_code0_sat_l hY υ (.bound 11) (.bound 12) (.bound 4) (.bound 13)).mpr
      (tt_code0_source_l hY vt nv υV (.bound 11) (.bound 12) (.bound 4) (.bound 13) q)
  · let ix : Fin 3 → Fin 17 := Fin.cases 9 (Fin.cases 8 (fun _ => 3))
    let f : Fin 3 → Term 17 := Fin.cases (.bound 9) (Fin.cases (.bound 8) (fun _ => .bound 3))
    exact move tg_guard_program0_m tg_guard_program0_closed_l ix f
      (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))
      (Fin.cases (Or.inl hω) (Fin.cases (Or.inr hl) (fun _ => Or.inr hh))) ph
  · have q := column _ (by simp -implicitDefEqProofs)
      (tg_guard_code_reflect_l hX ut nu εU (.bound 11) (.bound 10) (.bound 12) (.bound 8) (.bound 3) (.bound 14) hA names ch₀)
    exact (tg_guard_code_sat_l hY υ (.bound 11) (.bound 10) (.bound 12) (.bound 8) (.bound 3) (.bound 14)).mpr
      (tg_guard_code_source_l hY vt nv υV (.bound 11) (.bound 10) (.bound 12) (.bound 8) (.bound 3) (.bound 14) q)
  · let ix : Fin 2 → Fin 17 := Fin.cases 9 (fun _ => 2)
    let f : Fin 2 → Term 17 := Fin.cases (.bound 9) (fun _ => .bound 2)
    exact move ee_inacc_program0_m ee_inacc_program0_closed_l ix f
      (Fin.cases rfl (fun _ => rfl)) (Fin.cases (Or.inl hω) (fun _ => Or.inr hi)) pi
  · let φ : Formula 1 17 := kpair0_m (.bound 0) (.bound 9) (.bound 9)
    have q := column φ (by simp -implicitDefEqProofs [φ])
      ((rt_model_delta_l ut nu (kpair0_delta_l ..) εU).mpr pair)
    exact (rt_model_delta_l vt nv (kpair0_delta_l ..) υV).mp q
  · have q := column _ (by simp -implicitDefEqProofs)
      (tt_code2_reflect_l hX ut nu omega hwU εU (.bound 11) (.bound 12) (.bound 2) (.bound 15) (.bound 11) (.bound 0) hA names ci₀)
    exact (tt_code2_sat_l hY υ (.bound 11) (.bound 12) (.bound 2) (.bound 15) (.bound 11) (.bound 0)).mpr
      (tt_code2_source_l hY vt nv υV (.bound 11) (.bound 12) (.bound 2) (.bound 15) (.bound 11) (.bound 0) q)
  · let ix : Fin 6 → Fin 17 := Fin.cases 9 (Fin.cases 11 (Fin.cases 7 (Fin.cases 6 (Fin.cases 5 (fun _ => 1)))))
    let f : Fin 6 → Term 17 := Fin.cases (.bound 9) (Fin.cases (.bound 11) (Fin.cases (.bound 7)
      (Fin.cases (.bound 6) (Fin.cases (.bound 5) (fun _ => .bound 1)))))
    exact move ee_stretch_program0_m ee_stretch_program0_closed_l ix f
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))))))
      (Fin.cases (Or.inl hω) (Fin.cases (Or.inr hn) (Fin.cases (Or.inr hv) (Fin.cases (Or.inr hd)
        (Fin.cases (Or.inr he) (fun _ => Or.inr hz)))))) pe
  · have q := column _ (by simp -implicitDefEqProofs)
      (ee_stretch_code_reflect_l hX.1 ut nu εU (.bound 9) (.bound 11) (.bound 10) (.bound 7)
        (.bound 6) (.bound 5) (.bound 1) (.bound 16) ce₀)
    exact (ee_stretch_code_sat_l hY.1 υ (.bound 9) (.bound 11) (.bound 10) (.bound 7)
      (.bound 6) (.bound 5) (.bound 1) (.bound 16)).mpr
        (ee_stretch_code_source_l hY.1 vt nv υV (.bound 9) (.bound 11) (.bound 10) (.bound 7)
          (.bound 6) (.bound 5) (.bound 1) (.bound 16) q)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原生旧轮语言在共同层中的完整像

先给原常量域、全部有限列和四条查询求共同秩界，再逐个搬运原对象。
目标有限列的反向包含由子集闭性回收；数值程序随后恢复完整语言。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_common_d.language_model_l
    {Ω b B R₀ c X R d Y S j k w₀ z₀ w z w' z' L l U V Γ t : M.Domain}
    (common : Ic_common_d I X R Y S L l U V Γ t)
    (hΩ : M.IsOmega Ω) (mb : Smdl_d I b B R₀) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (zx : (smdl_structure_l I (R := R) mx.2.1).Models ZF)
    (hZY : (smdl_structure_l I (R := S) my.2.1).Models ZFC)
    (left : Smap_d I Ω b c B X j) (right : Smap_d I Ω b d B Y k) (ext : Rf_ext_d I B R₀)
    (root : Rr_layer_d I Ω B R₀ w₀ z₀) (source : Rr_layer_d I Ω X R w z)
    (target : Rr_layer_d I Ω Y S w' z')
    (ρ : Env (smdl_structure_l I (R := R) mx.2.1) 10)
    (hw : (ρ.bound 0).val = w) (hk : Rd_entry_d (ρ.bound 1).val U R)
    (valid : Formula.satisfies ρ ee_language0_m) :
    (∀ i, Rd_entry_d (ρ.bound i).val U R) ∧
    ∃ θ : Env (smdl_structure_l I (R := S) my.2.1) 10,
      (∀ i, Rd_entry_d (ρ.bound i).val (θ.bound i).val t) ∧
      (θ.bound 0).val = w' ∧ Formula.satisfies θ ee_language0_m := by
  let Xn := smdl_structure_l I (R := R) mx.2.1
  let Yn := smdl_structure_l I (R := S) my.2.1
  have zy := ZFC.models_zf_l hZY
  have hX := ZF.modelsKP zx
  have hY := ZF.modelsKP zy
  let Un : Xn.Domain := ⟨U,common.left_rank.2.1⟩
  let wn : Xn.Domain := ⟨w,source.member⟩
  let wn' : Yn.Domain := ⟨w',target.member⟩
  have hwN : ρ.bound 0 = wn := Subtype.ext hw
  have ru := (rr_rank_native_l I mx.2.1 hX (⟨L,common.left_rank.1⟩ : Xn.Domain) Un).mp common.left_rank
  have limit : Xn.IsLimitOrdinal (⟨L,common.left_rank.1⟩ : Xn.Domain) :=
    (Formula.satisfies_isLimitOrdinal_iff ..).mp ((rr_truth_native_l I mx.2.1
      (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => (⟨L,common.left_rank.1⟩ : Xn.Domain))).mp common.limit)
  have omega := source.omega_l I (ZF.modelsKP hZF) hΩ hX.1
  have omega' := target.omega_l I (ZF.modelsKP hZF) hΩ hY.1
  have parts := valid
  simp only [ee_language0_m,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at parts
  obtain ⟨domain,lim,base,constants,hg,hh,hi,he,_,_,numeric⟩ := parts
  have lim := (Formula.satisfies_isLimitOrdinal_iff ..).mp lim
  have base := (v_sigma_sat_l hX ..).mp base
  have constants := (tt_constants0_sat_l hX.1 ..).mp constants
  simp only [ee_domain_pack_m,Formula.satisfies_bind,ee_domain_pack0_m,
    Formula.satisfies_conj_iff] at domain
  have pool := (tt_pool_sat_l (kp_pair_l hX) hX ..).mp domain.2.1
  have hω : Xn.IsOmega (ρ.bound 0) := hwN.symm ▸ omega
  have hn : Xn.mem (ρ.bound 2) (ρ.bound 0) := by
    have codes := numeric
    simp only [ee_numeric_m,Formula.satisfies_bind,ee_numeric0_m,Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff] at codes
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,p,_⟩ := codes
    simp only [ee_stretch_program_m,Formula.satisfies_bind,ee_stretch_program0_m,
      Formula.satisfies_conj_iff,Formula.satisfies_mem_iff] at p
    exact p.1
  have hB := ZF.v_mem_l (kp_pair_l hX) zx base ru
    (ZF.v_ordinal_height_l zx ru lim.1 hk)
  have hU := tt_constants_rank_l zx ru limit
    (ZF.v_ordinal_height_l zx ru lim.1 hk) base constants
  have hwU : Xn.mem wn Un := hwN ▸ v_subset_mem_l (kp_pair_l hX) ru hk
    (hω.subset_limitOrdinal hX lim)
  have ut := v_transitive_l (kp_pair_l hX) ru
  have hPool := pool.rank_mem_l hX hω ru limit (hwN.symm ▸ hwU) hn hU
  have low : ∀ i, Xn.mem (ρ.bound i) Un :=
    Fin.cases (hwN.symm ▸ hwU) (Fin.cases hk (Fin.cases (ut _ (hwN.symm ▸ hwU) _ hn)
      (Fin.cases hB (Fin.cases hU (Fin.cases hPool
        (Fin.cases (ut _ hPool _ hg) (Fin.cases (ut _ hPool _ hh)
          (Fin.cases (ut _ hPool _ hi) (Fin.cases (ut _ hPool _ he) (fun i => Fin.elim0 i))))))))))
  obtain ⟨A,E,names,seq,product⟩ := pool
  have hA := names.rank_mem_l hX hω ru limit (hwN.symm ▸ hwU) hn hU
  obtain ⟨D,hD,wd,ad⟩ := v_joint_bound_l (kp_pair_l hX) ru (low 0) hA
  have hE : Xn.mem E Un := v_relations_mem_l (kp_pair_l hX) ru limit hD (fun f hf p hp => by
    obtain ⟨n,hn,fn⟩ := (seq f).mp hf
    obtain ⟨a,b,pair⟩ := fn.1.1 p hp
    exact ⟨a,wd a (hω.transitive hX n hn a (fn.input_mem_of_pairMember ⟨p,pair,hp⟩)),
      b,ad b (fn.output_mem_of_pairMember ⟨p,pair,hp⟩),pair⟩)
  have ey := right.extensional_l hZF hΩ mb my ext
  have digits := common.layer_image_l (ZF.modelsKP hZF) mx.2.1 ey source target ut hwU
  let nu : Nonempty {x : Xn.Domain // Xn.mem x Un} := ⟨⟨wn,hwU⟩⟩
  have values (a : Xn.Domain) (ha : Xn.mem a Un) :
      ∃ y : Yn.Domain, Rd_entry_d a.val y.val t := by
    obtain ⟨y,hy,ay⟩ := common.injection.1.2.2 a.val ((common.carrier a.val).mpr ⟨a.property,ha⟩)
    exact ⟨⟨y,hy⟩,ay⟩
  obtain ⟨v,points⟩ := Classical.axiomOfChoice (fun i => values (ρ.bound i) (low i))
  let θ : Env Yn 10 := ⟨v,fun _ => wn'⟩
  have hw' : (θ.bound 0).val = w' := common.injection.1.1.2 w _ w' (hw ▸ points 0) digits.1
  have hwY : θ.bound 0 = wn' := Subtype.ext hw'
  obtain ⟨A',AA⟩ := values A hA
  obtain ⟨E',EE⟩ := values E hE
  have move {n} (φ : Formula 1 n) (closed : φ.FreeClosed) (delta : φ.IsDelta0)
      (a : Env Xn n) (b : Env Yn n) (ha : ∀ i, Xn.mem (a.bound i) Un)
      (ab : ∀ i, Rd_entry_d (a.bound i).val (b.bound i).val t) :
      Formula.satisfies a φ ↔ Formula.satisfies b φ := by
    let aU : Env (rt_model_l Un nu) n := ⟨fun i => ⟨a.bound i,ha i⟩,fun _ => ⟨wn,hwU⟩⟩
    exact (Formula.closed_env_l φ closed (ρ := a) (η := image_env_l Subtype.val aU) rfl).trans
      (rr_native_delta_l I mx.2.1 my.2.1 Un ut nu common.carrier common.injection common.pred
        φ closed delta aU b ab)
  have limκ' : Yn.IsLimitOrdinal (θ.bound 1) :=
    (KP.limit0_sat_l hY θ (.bound 1)).mp
      ((move (KP.limit0_m (.bound 1)) (by simp -implicitDefEqProofs) (KP.limit0_delta_l _) ρ θ low points).mp
        ((KP.limit0_sat_l hX ρ (.bound 1)).mpr lim))
  let an : Env Xn 3 := ⟨Fin.cases A (Fin.cases (ρ.bound 4) (fun _ => ρ.bound 2)),ρ.free⟩
  let bn : Env Yn 3 := ⟨Fin.cases A' (Fin.cases (θ.bound 4) (fun _ => θ.bound 2)),θ.free⟩
  have names' : Tn_names_d (θ.bound 2) (θ.bound 4) A' :=
    (tn_names0_sat_l hY bn (.bound 2) (.bound 1) .newest).mp
      ((move (tn_names0_m (.bound 2) (.bound 1) .newest) (by simp -implicitDefEqProofs)
        (tn_names0_delta_l ..) an bn (Fin.cases hA (Fin.cases (low 4) (fun _ => low 2)))
          (Fin.cases AA (Fin.cases (points 4) (fun _ => points 2)))).mp
            ((tn_names0_sat_l hX an (.bound 2) (.bound 1) .newest).mpr names))
  let ap : Env Xn 3 := ⟨Fin.cases (ρ.bound 5) (Fin.cases E (fun _ => ρ.bound 0)),ρ.free⟩
  let bp : Env Yn 3 := ⟨Fin.cases (θ.bound 5) (Fin.cases E' (fun _ => θ.bound 0)),θ.free⟩
  have product' : Yn.IsCartesianProduct (kp_pair_l hY) (θ.bound 5) (θ.bound 0) E' :=
    (sh_product_sat_l hY bp .newest (.bound 2) (.bound 1)).mp
      ((move (sh_product_m .newest (.bound 2) (.bound 1)) (by simp -implicitDefEqProofs)
        (sh_product_delta_l ..) ap bp (Fin.cases (low 5) (Fin.cases hE (fun _ => low 0)))
          (Fin.cases (points 5) (Fin.cases EE (fun _ => points 0)))).mp
            ((sh_product_sat_l hX ap .newest (.bound 2) (.bound 1)).mpr product))
  have seq' : Fseq_space_d (kp_pair_l hY) (θ.bound 0) A' E' := by
    intro f'
    constructor
    · intro hf'
      obtain ⟨f,hf,ff⟩ := (common.pred E.val E'.val EE f'.val).mp hf'
      let fn : Xn.Domain := ⟨f,(mx.2.2.2 f E.val hf).1⟩
      obtain ⟨n,hn,fnf⟩ := (seq fn).mp hf
      obtain ⟨n',nn⟩ := values n (ut _ (low 0) n hn)
      exact ⟨n',(common.pred _ _ (points 0) _).mpr ⟨n.val,hn,nn⟩,fn0_function_l hY
        (rr_native_function_l I mx.2.1 my.2.1 hX.1 hY.1 Un ut common.carrier common.injection
          common.pred n A fn n' A' f' nn AA ff (fn0_of_function_l hX fnf)).1⟩
    · rintro ⟨n',hn',fnf⟩
      obtain ⟨n,hn,nn⟩ := (common.pred _ _ (points 0) n'.val).mp hn'
      let n₀ : Xn.Domain := ⟨n,(mx.2.2.2 n (ρ.bound 0).val hn).1⟩
      obtain ⟨P,hP,prod⟩ := KP.v_product_exists_l hX ru limit (ut _ (low 0) n₀ hn) hA
      obtain ⟨f,_,ff,fn⟩ := rr_cross_capture_l I mx.2.1 my.2.1 hX hY.1 Un n₀ A P ut
        common.carrier common.injection common.image common.pred common.right_closed hP prod
        n' A' f' nn AA (fn0_of_function_l hY fnf)
      exact (common.pred E.val E'.val EE f'.val).mpr
        ⟨f.val,(seq f).mpr ⟨n₀,hn,fn0_function_l hX fn⟩,ff⟩
  obtain ⟨F,hF,cert⟩ := KP.v_history_inside_l hX ru limit hk hB base
  have rank : Vr_d Un (ρ.bound 1) (ρ.bound 3) := ⟨_,F,hB,hF,fun x _ => cert x⟩
  have rawRank := rr_native_rank_value_l I mx.2.1 my.2.1 hY.1 Un (ρ.bound 1) (ρ.bound 3)
    ut common.carrier common.injection common.image common.pred common.right_closed (low 1) (low 3)
    (points 1) (points 3)
      ((vr_sat_l hX ut ⟨⟨ρ.bound 1,low 1⟩⟩ _ (.bound 1) .newest).mpr rank)
  have fullRank := (rr_rank_native_l I my.2.1 hY (θ.bound 1) (θ.bound 3)).mp rawRank
  have constants' := (tt_constants0_sat_l hY.1 θ (.bound 1) (.bound 3) (.bound 4)).mp
    ((move (tt_constants0_m (.bound 1) (.bound 3) (.bound 4)) (by simp -implicitDefEqProofs)
      (tt_constants0_delta_l ..) ρ θ low points).mp
        ((tt_constants0_sat_l hX.1 ρ (.bound 1) (.bound 3) (.bound 4)).mpr constants))
  let pick : Fin 8 → Term 10 := Fin.cases (.bound 0) (Fin.cases (.bound 1) (Fin.cases (.bound 2)
    (Fin.cases (.bound 4) (Fin.cases (.bound 6) (Fin.cases (.bound 7)
      (Fin.cases (.bound 8) (fun _ => .bound 9)))))))
  have numeric := (Formula.satisfies_bind ρ pick ee_numeric0_m).mp numeric
  have linked : ∀ i, Rd_entry_d ((Definitional.Env.substitute ρ pick).bound i).val
      ((Definitional.Env.substitute θ pick).bound i).val t :=
    Fin.cases (points 0) (Fin.cases (points 1) (Fin.cases (points 2) (Fin.cases (points 4)
      (Fin.cases (points 6) (Fin.cases (points 7) (Fin.cases (points 8) (fun _ => points 9)))))))
  have moved := common.numeric_model_l hZF hΩ mb mx my hX hY left right ext root source target
    (Definitional.Env.substitute ρ pick) (Definitional.Env.substitute θ pick) linked hw A hA names numeric
  have numeric' := (ee_numeric_sat_l hZY θ (.bound 0) (.bound 1) (.bound 2) (.bound 4)
    (.bound 6) (.bound 7) (.bound 8) (.bound 9)).mp
      ((Formula.satisfies_bind θ pick ee_numeric0_m).mpr moved)
  have language' := numeric'.language_l zy (hwY.symm ▸ omega') limκ' fullRank constants'
    ⟨A',E',names',seq',product'⟩
      ((common.pred _ _ (points 5) _).mpr ⟨_,he,points 9⟩)
  exact ⟨low,θ,points,hw',(ee_language0_sat_l hZY θ).mpr language'⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原生模型间同一候选的共同层运输

语言给出低秩查询域；dcp 是该域的实际子集，故属于同一共同层。
其定义经整个切片同构传输，再由两侧配对闭性读回完整模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ic_common_d.candidate_model_l
    {Ω b B R₀ c X R d Y S j k w₀ z₀ w z w' z' L l U V Γ t : M.Domain}
    (common : Ic_common_d I X R Y S L l U V Γ t)
    (hΩ : M.IsOmega Ω) (mb : Smdl_d I b B R₀) (mx : Smdl_d I c X R) (my : Smdl_d I d Y S)
    (zx : (smdl_structure_l I (R := R) mx.2.1).Models ZF)
    (zy : (smdl_structure_l I (R := S) my.2.1).Models ZFC)
    (left : Smap_d I Ω b c B X j) (right : Smap_d I Ω b d B Y k) (ext : Rf_ext_d I B R₀)
    (root : Rr_layer_d I Ω B R₀ w₀ z₀) (source : Rr_layer_d I Ω X R w z)
    (target : Rr_layer_d I Ω Y S w' z')
    (ρ : Env (smdl_structure_l I (R := R) mx.2.1) 12)
    (hw : (ρ.bound 2).val = w) (hk : Rd_entry_d (ρ.bound 3).val U R)
    (hu : Rd_entry_d (ρ.bound 0).val U R) (hn : Rd_entry_d (ρ.bound 1).val w R)
    (valid : Formula.satisfies ρ tg_candidate0_m) :
    ∃ θ : Env (smdl_structure_l I (R := S) my.2.1) 12,
      (∀ i, Rd_entry_d (ρ.bound i).val (θ.bound i).val t) ∧
      (θ.bound 2).val = w' ∧ Formula.satisfies θ tg_candidate0_m := by
  let N := smdl_structure_l I (R := R) mx.2.1
  let P := smdl_structure_l I (R := S) my.2.1
  have hN := ZF.modelsKP zx
  have hP := ZF.modelsKP (ZFC.models_zf_l zy)
  obtain ⟨lang,elastic⟩ := (Formula.satisfies_conj_iff ..).mp valid
  obtain ⟨low,ε,images,ew,lang'⟩ := common.language_model_l hZF hΩ mb mx my zx zy left right ext
    root source target (ρ.reindex fun i => i.succ.succ) hw hk ((Formula.satisfies_rename ..).mp lang)
  let Un : N.Domain := ⟨U,common.left_rank.2.1⟩
  let Vn : P.Domain := ⟨V,common.right_rank.2.1⟩
  let Ln : N.Domain := ⟨L,common.left_rank.1⟩
  have ru := (rr_rank_native_l I mx.2.1 hN Ln Un).mp common.left_rank
  have rv := (rr_rank_native_l I my.2.1 hP (⟨l,common.right_rank.1⟩ : P.Domain) Vn).mp common.right_rank
  have ut := v_transitive_l (kp_pair_l hN) ru
  have vt := v_transitive_l (kp_pair_l hP) rv
  have lim : N.IsLimitOrdinal Ln := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mx.2.1 (Formula.isLimitOrdinal .newest)
      (by simp -implicitDefEqProofs) (fun _ : Fin 1 => Ln)).mp common.limit)
  have values (x : N.Domain) (hx : N.mem x Un) : ∃ y : P.Domain, Rd_entry_d x.val y.val t := by
    obtain ⟨y,hy,xy⟩ := common.injection.1.2.2 x.val ((common.carrier _).mpr ⟨x.property,hx⟩)
    exact ⟨⟨y,hy⟩,xy⟩
  have hnU : N.mem (ρ.bound 1) Un := ut _ (low 0) _ ((congrArg (fun x => Rd_entry_d _ x R) hw).mpr hn)
  obtain ⟨u',iu⟩ := values (ρ.bound 0) hu
  obtain ⟨n',inn⟩ := values (ρ.bound 1) hnU
  let θ := ε.push n' |>.push u'
  have points : ∀ i, Rd_entry_d (ρ.bound i).val (θ.bound i).val t :=
    Fin.cases iu (Fin.cases inn images)
  have all : ∀ i, N.mem (ρ.bound i) Un := Fin.cases hu (Fin.cases hnU low)
  have all' (i) : P.mem (θ.bound i) Vn := (common.image _).mpr
    ⟨_,common.injection.1.input_mem_of_pairMember (points i),points i⟩
  let nu : Nonempty {x : N.Domain // N.mem x Un} := ⟨⟨ρ.bound 0,hu⟩⟩
  let nv : Nonempty {x : P.Domain // P.mem x Vn} := ⟨⟨θ.bound 0,all' 0⟩⟩
  let a : Env (rt_model_l Un nu) 12 := ⟨fun i => ⟨ρ.bound i,all i⟩,fun _ => ⟨ρ.bound 0,hu⟩⟩
  let b : Env (rt_model_l Vn nv) 12 := ⟨fun i => ⟨θ.bound i,all' i⟩,fun _ => ⟨θ.bound 0,all' 0⟩⟩
  let φ : Formula 1 12 :=
    tg_elastic_m (.bound 4) (.bound 1) (.bound 7) (.bound 8) (.bound 9) (.bound 10) (.bound 11) (.bound 0)
  obtain ⟨v,drop,ev⟩ := (tg_elastic_sat_l (kp_pair_l hN) hN.1 ..).mp elastic
  have hv : N.mem v Un := v_subset_mem_l (kp_pair_l hN) ru (low 5)
    (fun p hp => ((drop.2 p).mp hp).1)
  let vU : (rt_model_l Un nu).Domain := ⟨v,hv⟩
  have reflected : Formula.satisfies a φ := by
    simp only [φ,tg_elastic_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff]
    exact ⟨vU,(td_dcp_source_l hN.1 (KP.exists_pair hN) ut nu (sc_v_pair_l hN lim ru)
      (a.push vU) (.bound 5) (.bound 2) (.bound 8) (.bound 1) (.bound 0)).mpr drop,
      (ee_elastic_absolute_l ut nu (a.push vU)
        (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 0)).mpr ev⟩
  have moved := (rr_native_slice_l I mx.2.1 my.2.1 Un Vn nu nv common.carrier common.injection
    common.image common.pred φ (by simp -implicitDefEqProofs [φ]) a b points).mp reflected
  simp only [φ,tg_elastic_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff] at moved
  obtain ⟨vV,drop',ev'⟩ := moved
  have drop' := (td_dcp_source_l hP.1 (KP.exists_pair hP) vt nv
    (common.pair_native_l hZF mx my hN)
    (b.push vV) (.bound 5) (.bound 2) (.bound 8) (.bound 1) (.bound 0)).mp drop'
  have ev' := (ee_elastic_absolute_l vt nv (b.push vV)
    (.bound 9) (.bound 10) (.bound 11) (.bound 12) (.bound 0)).mp ev'
  refine ⟨θ,points,ew,(Formula.satisfies_conj_iff ..).mpr ⟨?_,?_⟩⟩
  · exact (Formula.satisfies_rename ..).mpr
      ((Formula.closed_env_l ee_language0_m ee_language0_closed_l rfl).mp lang')
  · exact (tg_elastic_sat_l (kp_pair_l hP) hP.1 ..).mpr ⟨vV.val,drop',ev'⟩

end YesMetaZFC.SetTheory.LargeCardinal
