import YesMetaZFC.SetTheory.LargeCardinal.Game.Subtype
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.Model.SetTheory.Relations.Small
import YesMetaZFC.Model.SetTheory.Relations.Hierarchy
import YesMetaZFC.Model.SetTheory.Relations.Parity
import YesMetaZFC.SetTheory.LargeCardinal.Game.IterationStep
import YesMetaZFC.SetTheory.LargeCardinal.Game.Basis
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CriticalBound
import YesMetaZFC.Model.SetTheory.Internal.MembershipSlice
import YesMetaZFC.SetTheory.LargeCardinal.Game.Rank
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.SetTheory.LargeCardinal.Game.IterationSyntax

/-! # 给定地模型内部的初始反射上下文

有限反射在给定模型中实施，所得层及其完整更新核直接还原到外部。
构造不更换工作根，也不要求给定模型对外部可数序列封闭。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {X : M.Domain}
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

include hZF in
theorem tg_context_relative_l {c R : M.Domain} (model : Smem_d I c X R)
    (hX : M.TransitiveSet X) (nx : Nonempty {x // M.mem x X})
    (ground : (rt_model_l X nx).Models ZFC) (ω A : (rt_model_l X nx).Domain)
    (hω : M.IsOmega ω.val) (Φ : List Lr_formula) :
    ∃ η C : (rt_model_l X nx).Domain, Tg_context_d I ω.val X R η.val C.val ∧ M.mem A.val C.val ∧ Sc_small_d X C.val ∧
      Fs_read_d ω.val C.val ∧ ∀ q ∈ Φ, Lr_reflect_d q.2.val C := by
  let hN := ZFC.models_zf_l ground
  let J := kp_pair_l (ZF.modelsKP hN)
  obtain ⟨P, pair⟩ := KP.exists_pair (ZF.modelsKP hN) ω A
  obtain ⟨η, C, rank, limit, hP, reflect⟩ := ZF.lr_finite_l J hN (⟨0, tg_kernel_m, tg_kernel_closed_l⟩ :: Φ) P
  have trans := v_transitive_l J rank
  have hωC := trans P hP ω ((pair ω).mpr (Or.inl rfl))
  have hAC := trans P hP A ((pair A).mpr (Or.inr rfl))
  let ρ : Env (rt_model_l X nx) 0 := ⟨Fin.elim0, fun _ => ω⟩
  have valid := (reflect ⟨0, tg_kernel_m, tg_kernel_closed_l⟩ (List.mem_cons_self ..)
    ρ (fun i => Fin.elim0 i)).mp (tg_kernel_true_l ground ω)
  have kernel := (rt_model_delta_l hX nx tg_context_delta_l (ρ.push C)).mp valid
  let τ : Env (rt_model_l X nx) 2 := ⟨Fin.cases C (fun _ => η), fun _ => ω⟩
  have relative := (vr_sat_l (ZF.modelsKP hZF) hX nx τ (.bound 1) .newest).mp
    ((v_sigma_sat_l (ZF.modelsKP hN) τ (.bound 1) .newest).mpr rank)
  -- 在给定模型内取序数枚举与最小原像；编号图仍属于该模型。
  obtain ⟨μ, f, ord, fn, onto⟩ := ZFC.ordinal_enum_l ground J C
  obtain ⟨g, inj, _⟩ := ZF.exists_rightInverseInjection_of_surjection_from_ordinal hN J ord fn onto
  let ξ : Env (rt_model_l X nx) 3 := ⟨Fin.cases g (Fin.cases C (fun _ => μ)), fun _ => ω⟩
  have index := (sc_index_sat_l (ZF.modelsKP hN) ξ (.bound 2) (.bound 1) .newest).mpr
    (Sc_index_d.of_injection_l (ZF.modelsKP hN) ord inj)
  have moved := (rt_model_delta_l hX nx (sc_index_delta_l (.bound 2) (.bound 1) .newest) ξ).mp index
  have small : Sc_small_d X C.val := ⟨μ.val, g.val, μ.property, g.property,
    (sc_index_sat_l (ZF.modelsKP hZF) (image_env_l (M := rt_model_l X nx) (N := M) Subtype.val ξ)
      (.bound 2) (.bound 1) .newest).mp moved⟩
  have limit := (rt_limit_l hX nx (ZF.modelsKP hZF) η).mp limit
  have finite := fs_rank_relative_l hZF hX nx hN ω hω C.property relative limit hωC
  have kernel := (Formula.closed_env_l tg_context_m tg_context_closed_l
    (ρ := image_env_l Subtype.val (ρ.push C))
    (η := ((⟨Fin.elim0, fun _ => ω.val⟩ : Env M 0).push C.val))
    (funext (Fin.cases rfl (fun i => Fin.elim0 i)))).mp kernel
  exact ⟨η, C, Tg_context_d.of_mem_l (ZF.modelsKP hZF) hX model η.property C.property relative limit finite kernel,
    hAC, small, finite, fun q hq => reflect q (List.mem_cons_of_mem _ hq)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 给定根上的恒等图和共同低层实现

根载体就是给定 X。实现图是根恒等图在反射层上的实际限制；它覆盖该层的
全部成员和全部前驱，并满足后继构造已有的内在秩、小性及子集闭包条件。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.root_relative_l {ω c X R η C : M.Domain} (context : Tg_context_d I ω X R η C)
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (small : Sc_small_d X C) (model : Smem_d I c X R) :
    ∃ π k, Smap_d I ω c c X X π ∧
      (∀ x, M.mem x X → Rd_entry_d x x π) ∧ Rr_layer_d I C X R C k ∧
      Rr_closed_d I X R C ∧ Rr_small_d I X R C ∧ Rr_rank_d I X R η C := by
  obtain ⟨π, embed, spec⟩ := smap_identity_l I hZF (c := c) (X := X) hω
  have fixed x (hx : M.mem x X) := (spec x x).mpr ⟨hx, rfl⟩
  have ct := (context.rank_l (ZF.modelsKP hZF) hX ⟨c, model⟩).transitive_l hX context.member
  obtain ⟨k, layer, _⟩ := rr_layer_mem_l I hZF model hX context.member ct
  refine ⟨π, k, embed, fixed, layer,
    embed.subsets_raw_l I hZF hω hX model model.1 (fixed C context.member)
      (fun _ _ ha hb sub => (context.rank_l (ZF.modelsKP hZF) hX ⟨c, model⟩).subset_mem_l hX context.member ha hb sub),
    embed.small_raw_l hZF hω hX model model.1 (fixed C context.member) ct small, ?_⟩
  · obtain ⟨m, valid⟩ := context.rank
    exact ⟨m 1, m 0, (Formula.closed_env_l _ (by simp -implicitDefEqProofs)
      (funext (Fin.cases rfl (fun _ => rfl)))).mp valid⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 实际首行与零轮请求构造共同有限初态

原树仍取给定模型的单根树。工作复制由真实首行启动，空档案、原生空序数
历史界和背景空前缀分别从对象模型中构造，不把所属模型的空集当成背景空集。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_context_d.iteration_start_l
    {ω c X R w η C z o m T Q G q C₀ S₀ γ Bγ A B σ u U β : M.Domain}
    (context : Tg_context_d I w X R η C) (model : Smdl_d I c X R)
    (hN : (smdl_structure_l I (R := R) model.2.1).Models KP)
    (numbers : Rr_layer_d I ω X R w z)
    (nc : Nonempty {x : (smdl_structure_l I (R := R) model.2.1).Domain //
      (smdl_structure_l I (R := R) model.2.1).mem x ⟨C,context.member⟩})
    (ι : Env (rt_model_l (M := smdl_structure_l I (R := R) model.2.1) ⟨C,context.member⟩ nc) 46)
    (issued : Formula.satisfies ι tg_issued0_m) (hw : (ι.bound 0).val.val = w)
    (zero : ι.bound 19 = ι.bound 1) (empty : ∀ x, ¬ M.mem x o)
    (tree : It_tree_d hZF ω c m T Q G o) (succ : M.SuccessorOf m o)
    (node : Rd_entry_d o c Q) (root : It_map_d G o o q)
    (basis : Tg_basis_d I γ Bγ C₀ w X R C q)
    (name : M.PairMember I S₀ (ι.bound 7).val.val q)
    (alphabet : M.PairMember I A (ι.bound 6).val.val q) (letters : M.mem A Bγ)
    (lower : It_lower_d I γ X R (ι.bound 24).val.val)
    (row : Ic_row_d hZF ω c X B σ u U β) :
    ∃ H ST QT GT r f, Tg_iteration_d hZF ω c o C₀ S₀ γ Bγ A
      (fun i => [X,R,w,z,η,C,m,o,T,Q,G,o,o,o,(ι.bound 1).val.val,c,q,r,B,σ,H,ST,QT,GT,u,U,β,o,f].get i)
      (fun i => (ι.bound i).val.val) := by
  let N := smdl_structure_l I (R := R) model.2.1
  let Cn : N.Domain := ⟨C,context.member⟩
  let e : N.Domain := (ι.bound 1).val
  have fs := context.finite_l model.2.1 hN.1
  let J := rt_pair_l fs.transitive nc hN.1 fs.pair
  have rules := ((tg_issued_sat_l J (rt_model_ext_l hN.1 fs.transitive nc) ι).mp issued).control
  simp only [tg_control0_m,Formula.satisfies_conj_iff] at rules
  have rules := rules.2.2.1
  simp only [tg_rules_m,Formula.satisfies_conj_iff,Formula.satisfies_isEmpty_iff] at rules
  have he (x : N.Domain) (hx : N.mem x e) : False :=
    rules.2.1 ⟨x,fs.transitive _ (ι.bound 1).property x hx⟩ hx
  have hω := numbers.omega_l I (ZF.modelsKP hZF) tree.omega hN.1
  have heω := num_mem_l hN.1 hω (show Num_d 0 e from he)
  have ho := num_mem_l hZF.1 tree.omega (show Num_d 0 o from empty)
  obtain ⟨e',he',point⟩ := numbers.injection.1.2.2 o ho
  have ee : e' = e.val := congrArg Subtype.val (hN.1.eq_of_same_members (⟨e',he'⟩ : N.Domain) e
    (fun x => iff_of_false (fun hx => by
      obtain ⟨y,hy,_⟩ := (numbers.predecessors o e' point x.val).mp hx
      exact empty y hy) (he x)))
  have index : M.PairMember I o (ι.bound 19).val.val z :=
    Eq.mpr (congrArg (fun x => M.PairMember I o x z) (congrArg (fun x => x.val.val) zero)) (ee ▸ point)
  obtain ⟨m',H,ST,QT,GT,succ',history,first⟩ := row.start_l hZF tree.diagram empty node
  have em := succ'.eq hZF.1 succ
  subst m'
  have ord : Rr_truth_d I X R (KP.ord0_m .newest) (fun _ : Fin 1 => e.val) :=
    (rr_truth_native_l I model.2.1 (KP.ord0_m .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => e)).mpr ((KP.ord0_sat_l hN _ .newest).mpr (hω.members_areOrdinals hN e heω))
  have bound : Ic_bound_d I H Q X R σ o e.val :=
    ⟨ord,Or.inl (fun x hx h => he ⟨x,hx⟩ h),fun i _ hi _ => (empty i hi).elim⟩
  have ext : Rf_ext_d I X R := fun x hx y hy same =>
    congrArg Subtype.val (hN.1.eq_of_same_members (⟨x,hx⟩ : N.Domain) ⟨y,hy⟩ (fun t => same t.val t.property))
  have atlas := basis
  have cutoff := lower
  obtain ⟨_,g,V,sg,tg,hg,_,_,limit,_,_⟩ := atlas
  obtain ⟨g',s',hg',down⟩ := cutoff
  have eg := (hg.unique_l (ZF.modelsKP hZF) hg' ext).1
  have limit : N.IsLimitOrdinal ⟨g,hg.member⟩ := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I model.2.1 (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => (⟨g,hg.member⟩ : N.Domain))).mp limit)
  have below : M.PairMember I e.val (ι.bound 24).val.val R :=
    down e.val (eg ▸ limit.1.empty_mem_of_nonempty hN limit.2.1 he)
  have no_entry {i x} (h : M.PairMember I i x o) : False := h.elim fun p hp => empty p hp.2
  have seq : M.IsSequenceOfLength I o o :=
    ⟨tree.omega.members_areOrdinals (ZF.modelsKP hZF) o ho,
      ⟨fun p hp => (empty p hp).elim,fun _ _ _ hp _ => (no_entry hp).elim⟩,
      fun i => ⟨fun hi => (empty i hi).elim,fun ⟨x,hx⟩ => (no_entry hx).elim⟩⟩
  have levels i L : Rd_entry_d i L o ↔ ∃ p κ F, Rd_entry_d i p o ∧ It_payload_d p κ L F :=
    ⟨fun h => (no_entry h).elim,fun ⟨_,_,_,h,_⟩ => (no_entry h).elim⟩
  obtain ⟨r,record,values⟩ := rf_record_save_l I model.2.1 hN.1 tg_issued0_m tg_issued0_closed_l
    Cn fs.transitive fs.pair nc ι issued
  have map := tree.diagram.elementary o o q c X R c X R root node node model model
  obtain ⟨L,t,carrier,bijection,restriction⟩ := (basis.anchor_l I).alphabet_l hZF map.1.1.1 letters alphabet
  obtain ⟨f,play⟩ := context.prefix_l hZF model.2.1 hN.1 nc ι issued numbers index carrier bijection restriction
  refine ⟨H,ST,QT,GT,r.val,f,ho,succ,tree,history,seq.2.1,levels,first,node,model,node,root,basis,bound,
    ?_,alphabet,play,It_critical_bound_d.empty_l I empty⟩
  exact ⟨context,record,values,hw,tree.omega,numbers,ho,index,seq,
    (fun _ _ _ h _ => (no_entry h).elim),(fun _ _ _ h _ => (no_entry h).elim),
    ⟨q,root,name⟩,(fun _ _ h => (no_entry h).elim),lower,below⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 给定地模型中的实际零轮游戏记录

先解码给定模型的完整内部 ZFC 证书，导出全内部源理论，再在同一模型内
产生并反射控制记录。原模型码、树和策略逐项保留，根上使用同一个恒等图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {X : M.Domain}
  (hX : M.TransitiveSet X) (nx : Nonempty {x // M.mem x X})
local notation "N" => rt_model_l X nx
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF hX

theorem Tg_game_d.zero_relative_l {p : Tg_params_d (N).Domain} {c R : M.Domain}
    (hω : M.IsOmega p.ω.val) (model : Smem_d I c X R) (certificate : Zc_model_d I p.ω.val c X R)
    {A F L G D B W O Z g σ : (N).Domain}
    (game : Tg_game_d (certificate.membership_l I hZF hω model nx) p A F L G D B W O Z g)
    (woodin : Woodin_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.membership_l I hZF hω model nx)))) p.δ) (root : (N).mem p.e p.S)
    (win : Cg_win_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l
      (certificate.membership_l I hZF hω model nx)))) false p.ω A F D B W σ) :
    Sc_theory_d I p.ω.val X R ∧ Sc_collection_d I p.ω.val X R ∧ Sc_power_d X ∧
    (∃ K z, Er_source_d I p.ω.val p.ω.val p.ω.val K X R ∧ Rr_layer_d I p.ω.val X R p.ω.val z) ∧
    ∃ H η C r, M.mem H X ∧ Tg_context_d I p.ω.val X R η C ∧ Fs_read_d p.ω.val C ∧ Sc_small_d X C ∧
      Sc_power_d C ∧
      Rf_record_d I X R tg_issued0_m C r ∧ ∃ u : Fin 46 → M.Domain, Rf_tuple_d I X R u r ∧
        (∀ i, M.mem (u i) C) ∧
        (∀ i : Fin 19, u (i.castAdd 27) =
          [p.ω.val, p.e.val, p.a.val, p.b.val, p.c.val, p.δ.val, p.A.val, p.S.val, p.ν.val,
            p.E.val, p.P.val, p.Q.val, A.val, F.val, L.val, G.val, D.val, σ.val, H].get i) ∧
        u 19 = p.e.val ∧ u 23 = p.e.val ∧ u 26 = p.e.val ∧
        M.IsLimitOrdinal (u 24) ∧ Vr_d X (u 24) (u 29) ∧ M.mem p.ω.val (u 29) ∧ M.mem p.A.val (u 29) ∧
        ∃ π k, Smap_d I p.ω.val c c X X π ∧
          (∀ x, M.mem x X → Rd_entry_d x x π) ∧ Rr_layer_d I C X R C k ∧
          Rr_closed_d I X R C ∧ Rr_small_d I X R C ∧ Rr_rank_d I X R η C ∧
          ∃ α T Q G, M.SuccessorOf α p.e.val ∧ It_tree_d hZF p.ω.val c α T Q G p.e.val ∧
            Rd_entry_d p.e.val c Q ∧ It_map_d G p.e.val p.e.val π ∧
            It_lower_d I (u 24) X R (u 24) ∧ It_critical_bound_d I (u 24) Q p.e.val ∧
            Tg_basis_d I (u 24) (u 29) C p.ω.val X R C π ∧
            ∀ B σ z Z α, Ic_row_d hZF p.ω.val c X B σ z Z α →
              ∃ v, Tg_iteration_d hZF p.ω.val c p.e.val C p.S.val (u 24) (u 29) p.A.val v u ∧
                v 0 = X ∧ v 1 = R ∧ v 27 = p.e.val ∧
                ∃ s, Tg_iteration_code_d hZF p.ω.val c p.e.val C p.S.val (u 24) (u 29) p.A.val s ∧
                  Rt_coord_d (27 : Fin 75) s p.e.val := by
  have ground : (N).Models ZFC := certificate.membership_l I hZF hω model nx
  have power := certificate.power_l hZF hω hX model
  obtain ⟨z₀, numbers, _⟩ := rr_layer_mem_l I hZF model hX p.ω.property
    (hω.isOrdinal (ZF.modelsKP hZF)).transitive
  obtain ⟨K, source⟩ := certificate.source_l hZF hω numbers
  refine ⟨certificate.theory_l hZF hω, certificate.collection_l hZF hω, power, ⟨K, z₀, source, numbers⟩, ?_⟩
  -- 在原模型内生成控制记录，再反射原记录公式。
  obtain ⟨H, r, tuple, _, valid⟩ := Tg_game_d.control_l (M := N) ground (p := p) game woodin root win
  let φ : Formula 1 1 := rt_record_m tg_control0_m .newest
  have hc : φ.FreeClosed := rt_record_closed_l _ _ tg_control0_closed_l rfl
  obtain ⟨η, C, context, hr, small, fs, reflect⟩ :=
    tg_context_relative_l hZF model hX nx ground p.ω r hω [⟨1, φ, hc⟩]
  let ξ : Env N 1 := (⟨Fin.elim0, fun _ => p.ω⟩ : Env N 0).push r
  have truth : Formula.satisfies ξ φ := (Formula.closed_env_l φ hc
    (ρ := ((⟨Fin.elim0, fun _ => p.ω⟩ : Env N 0).push r)) (η := ξ) rfl).mp valid
  have reflection : Lr_reflect_d φ C := reflect ⟨1, φ, hc⟩ (List.mem_cons_self ..)
  have reflected := (reflection ξ (Fin.cases hr (fun i => Fin.elim0 i))).mp truth
  have record : Rt_record_in_d tg_control0_m C r := by
    apply (Formula.satisfies_conj_iff ..).mpr
    refine ⟨hr, ?_⟩
    exact (Formula.closed_env_l _ (lr_rel_closed_l φ hc .newest (fun i => .bound i.succ)
      rfl (fun _ => rfl)) (ρ := ξ.push C)
      (η := ⟨Fin.cases C (fun _ => r), fun _ => C⟩)
      (funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))).mp reflected
  -- 相对记录是有界公式；先作绝对化，再显式识别绑定赋值。
  let θ : Env N 2 := ⟨Fin.cases C (fun _ => r), fun _ => C⟩
  have moved := (rt_model_delta_l hX nx (rt_record_in0_delta_l tg_control0_m) θ).mp record
  have record : Rt_record_in_d (M := M) tg_control0_m C.val r.val := by
    change Formula.satisfies (⟨Fin.cases C.val (fun _ => r.val), fun _ => C.val⟩ : Env M 2)
      (rt_record_in0_m tg_control0_m)
    exact (Formula.closed_env_l (rt_record_in0_m tg_control0_m) (rt_record_in0_closed_l _ tg_control0_closed_l)
      (ρ := @image_env_l N M Subtype.val 2 θ)
      (η := (⟨Fin.cases C.val (fun _ => r.val), fun _ => C.val⟩ : Env M 2))
      (funext (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))).mp moved
  let v : Fin 19 → (N).Domain := fun i =>
    [p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q, A, F, L, G, D, σ, H].get i
  have tuple : Rt_tuple_d (fun i => (v i).val) r.val := (rt_tuple_source_l hZF.1 hX nx v r).mp tuple
  let nc : Nonempty {x // M.mem x C.val} := ⟨⟨p.ω.val, (context.omega_l ⟨c, model⟩)⟩⟩
  obtain ⟨_, a, code, control⟩ := (rt_record_in_read_l hZF.1 tg_control0_m tg_control0_closed_l fs.transitive nc).mp record
  let ρ : Env (rt_model_l C.val nc) 19 := ⟨a, fun _ => a 0⟩
  have eqρ (i) : (ρ.bound i).val = (v i).val := congrFun (rt_tuple_inj_l code tuple) i
  -- 读取同一个首轮请求，有限配对足以把全部坐标重新保存。
  let Kp := rt_pair_l fs.transitive nc hZF.1 fs.pair
  have ext := rt_model_ext_l hZF.1 fs.transitive nc
  obtain ⟨a, h, j, _, _, _, _, _, _, _, _, _, w, seed, hw, _, _, _, _, hk, _, _, ht, _,
    _, _, _, letters, ℓ, issued⟩ := tg_control_start_l Kp ext ρ control
  let ε : Env (rt_model_l C.val nc) 38 := ⟨w, ρ.free⟩
  let ι := tg_issued_start_env_d ρ ε a h ℓ j
  let X₀ := smdl_structure_l I (R := R) model.1.2.1
  let C₀ : X₀.Domain := ⟨C.val, context.member⟩
  let nd : Nonempty {x : X₀.Domain // X₀.mem x C₀} :=
    ⟨⟨⟨p.ω.val, p.ω.property⟩, (model.2 p.ω.val C.val).mpr ⟨p.ω.property, context.member, (context.omega_l ⟨c, model⟩)⟩⟩⟩
  have inside := hX C.val context.member
  let ι₀ := model.native_env_d I C₀ inside nd nc ι
  have issued₀ := (model.native_formula_l I C₀ inside nd nc tg_issued0_m ι).mp issued
  obtain ⟨s₀, saved, values⟩ := rf_record_save_l I model.1.2.1 (certificate.ext.native_l I model.1.2.1)
    tg_issued0_m tg_issued0_closed_l C₀ (model.slice_transitive_l I C₀ fs.transitive)
      (model.slice_pair_l I C₀ inside fs.pair) nd ι₀
      issued₀
  let s := s₀.val
  -- 原语言给出相对 Vκ；原回答的所属扩展器给出 ω∈κ。
  have facts := seed
  simp only [tg_seed0_m, tg_seed_m, Formula.satisfies_conj_iff] at facts
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, language, _⟩ := facts
  let pick : Fin 10 → Term 38 := fun i => [.bound 0, .bound 5, .bound 7, .bound 14, .bound 15,
    .bound 16, .bound 27, .bound 28, .bound 29, .bound 30].get i
  let ζ := Definitional.Env.substitute ε pick
  have language : Formula.satisfies ζ ee_language0_m := (Formula.satisfies_bind ε pick ee_language0_m).mp language
  simp only [ee_language0_m, Formula.satisfies_conj_iff] at language
  have limit := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) (w 5)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp language.2.1)
  have inner := (vr_sat_l (ZF.modelsKP hZF) fs.transitive nc ζ (.bound 1) (.bound 3)).mp language.2.2.1
  have rank := (context.rank_l (ZF.modelsKP hZF) hX ⟨c, model⟩).of_rank_l hX context.member (w 14).property inner
  have below : M.mem p.ω.val (w 5).val := (congrArg Subtype.val hw).trans (eqρ 0) ▸
    tg_successor_omega_l ε ((context.kernel_mem_l hX ⟨c, model⟩ fs.transitive nc).renew_l ε seed)
  -- 原给定模型本身成为根，原空序数标号与根恒等图同时进入实际树。
  have empty (x : M.Domain) (hx : M.mem x p.e.val) : False :=
    game.setup.empty ⟨x, hX p.e.val p.e.property x hx⟩ hx
  have ready : It_source_d hZF p.ω.val c := ⟨hω, X, R, p.ω.val, K, z₀, model.1, source, numbers⟩
  obtain ⟨z, α, T₀, Q₀, G₀, hz, step, tree⟩ := it_root_l hZF ready
  have ez := hZF.1.eq_of_same_members z p.e.val (fun x => iff_of_false (hz x) (empty x))
  rw [ez] at step tree
  have node := tree.root p.e.val empty
  obtain ⟨π, edge⟩ := tree.diagram.map_l hZF (tree.diagram.order.refl p.e.val step.predecessor_mem)
  have map := tree.diagram.elementary p.e.val p.e.val π c X R c X R edge node node model.1 model.1
  have fixed x (hx : M.mem x X) : Rd_entry_d x x π := by
    obtain ⟨y, _, hxy⟩ := map.1.1.2.2 x hx
    have eq := tree.diagram.identity p.e.val π edge x y hxy
    cases eq
    exact hxy
  obtain ⟨_, k, _, _, layer, closed, sizes, rankC⟩ := context.root_relative_l hZF hω hX small model
  have hωB := rank.ordinal_subset_l hZF hX (hX C.val C.property _ (w 14).property) p.ω.val below
  have basis := Tg_basis_d.of_mem_l hZF model hX (hX C.val C.property _ (w 5).property)
    (hX C.val C.property _ (w 14).property) limit rank hωB (fixed C.val C.property)
    (fun x hx => fixed x (hX _ (hX C.val C.property _ (w 14).property) x hx))
  have low := It_lower_d.mem_l I hZF model hX (hX C.val C.property _ (w 5).property) limit.1
    (hX C.val C.property _ (w 5).property) (fun _ h => h)
  refine ⟨H.val, η.val, C.val, s, H.property, context, fs, small,
    power.rank_l hX context.member (context.rank_l (ZF.modelsKP hZF) hX ⟨c, model⟩) (context.limit_l (ZF.modelsKP hZF) hX ⟨c, model⟩), saved,
    (fun i => (ι.bound i).val), values, (fun i => (ι.bound i).property), ?_, eqρ 1,
    (congrArg Subtype.val ht).trans (eqρ 1), (congrArg Subtype.val hk).trans (eqρ 1),
    limit, rank, rank.ordinal_subset_l hZF hX (hX C.val C.property _ (w 14).property) p.ω.val below,
    eqρ 6 ▸ letters, π, k, map, fixed, layer, closed, sizes, rankC, α, T₀, Q₀, G₀, step, tree, node, edge, low,
    It_critical_bound_d.empty_l I empty, basis,?_⟩
  · intro i
    simp only [ι, tg_issued_start_env_d, Fin.addCases_left]
    rw [eqρ]
    change Subtype.val (([p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q, A, F, L, G, D, σ, H]).get i) = _
    exact (List.getElem_map Subtype.val
      (l := [p.ω, p.e, p.a, p.b, p.c, p.δ, p.A, p.S, p.ν, p.E, p.P, p.Q, A, F, L, G, D, σ, H])
      (i := i.val) (h := i.isLt)).symm
  · intro B σ z Z α row
    have hN := ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hω))
    have name : Rd_entry_d p.S.val (ι₀.bound 7).val.val π :=
      Eq.mpr (congrArg (fun S => Rd_entry_d p.S.val S π) (eqρ 7)) (fixed p.S.val p.S.property)
    have alphabet : Rd_entry_d p.A.val (ι₀.bound 6).val.val π :=
      Eq.mpr (congrArg (fun A => Rd_entry_d p.A.val A π) (eqρ 6)) (fixed p.A.val p.A.property)
    obtain ⟨H',ST,QT,GT,r',f,start⟩ := context.iteration_start_l hZF model.1 hN numbers nd ι₀
      issued₀ (eqρ 0) rfl empty tree step node edge basis name alphabet (eqρ 6 ▸ letters) low row
    obtain ⟨s,pack,code⟩ := start.pack_l hZF
    exact ⟨_,start,rfl,rfl,rfl,s,code,_,pack,rfl⟩

end YesMetaZFC.SetTheory.LargeCardinal
