import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.WoodinTypeStep
import YesMetaZFC.SetTheory.LargeCardinal.Demand.Setup
import YesMetaZFC.SetTheory.LargeCardinal.Demand.HistoryConstruction
import YesMetaZFC.SetTheory.LargeCardinal.Types.OneStep
import YesMetaZFC.SetTheory.Descriptive.Game.ClosedDeterminacy
import YesMetaZFC.SetTheory.Descriptive.Game.GameAttemptRank
import YesMetaZFC.SetTheory.LargeCardinal.Game.GenericPreparation

/-! # 任意下界以上的 demanding 游戏实际重置走法

先在原 Vδ 内找到包含固定字母表 A 的低层，再与给定下界共同送入武丁
工厂。固定查询表读取 (κ,0,空图,A)，两组空标签的节点真值直接来自原根。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Td_setup_d.reset_move_l {p : Tg_params_d M.Domain} {X χ : M.Domain}
    (setup : Td_setup_d hZFC p X) (hd : Woodin_d I p.δ) (root : M.mem p.e p.S) (hχ : M.mem χ p.δ) :
    ∃ κ C a u, M.mem χ κ ∧ M.mem κ p.δ ∧ V_d I κ C ∧ M.mem a X ∧ Td_move_d a p.e p.e κ u ∧
      ∀ n h z, Tg_digits_d hZF p.c p.b n p.A h z →
        Td_growth_d hZF p.e p.c p.A n h κ C → Td_aux_d hZF p n h a := by
  have heω := num_mem_l hZF.1 setup.omega (show Num_d 0 p.e from setup.empty)
  obtain ⟨ξ,Z₀,hξ,hZ₀,hAZ₀⟩ := (ZF.v_limit_mem_l I hZF setup.rank setup.limit.2.2 p.A).mp setup.letters
  obtain ⟨ζ,hζ,hχζ,hξζ⟩ : ∃ ζ, M.mem ζ p.δ ∧
      (χ = ζ ∨ M.mem χ ζ) ∧ (ξ = ζ ∨ M.mem ξ ζ) := by
    rcases setup.limit.1.wellOrder.linear.compare χ hχ ξ hξ with eq | lt | gt
    · exact ⟨ξ,hξ,Or.inl (hZF.1.eq_of_same_members χ ξ eq),Or.inl rfl⟩
    · exact ⟨ξ,hξ,Or.inr lt,Or.inl rfl⟩
    · exact ⟨χ,hχ,Or.inl rfl,Or.inr gt⟩
  obtain ⟨dν,Z,hZ,hSZ⟩ := setup.low.read_l hZF setup.limit.1
  obtain ⟨ω,l,μ,Y,c,R,hw,hl,hμ,hY,model,all⟩ :=
    woodin_game_reset_l hZFC hd hZ dν hSZ setup.empty root
  have eq := hZF.1.eq_of_same_members ω p.ω (fun x =>
    ⟨hw.2 p.ω setup.omega.1 x,setup.omega.2 ω hw.1 x⟩)
  subst ω
  have eq := hl.eq hZF.1 setup.one
  subst l
  obtain ⟨m,κ,C,U,D,P,r,u,_,_,_,q,hm,high,hκ,language,full,elastic,first,last,_,_,_,_,_,_⟩ := all ζ hζ
  have eq := hm.eq hZF.1 setup.two
  subst m
  have above : M.mem χ κ := hχζ.elim (fun eq => eq.symm ▸ high) (language.limit.1.transitive ζ high χ)
  have hξκ : M.mem ξ κ := hξζ.elim (fun eq => eq.symm ▸ high) (language.limit.1.transitive ζ high ξ)
  have hAC := ZF.v_mono_l I hZF hZ₀ language.rank (language.limit.1.transitive ξ hξκ) p.A hAZ₀
  have hAU := (language.constants p.A).mpr (Or.inl hAC)
  have haω := setup.omega.transitive (ZF.modelsKP hZF) p.b full.finite p.a setup.two.predecessor_mem
  -- 弹性语义转到开局已取定的同一代码表，不改动完整重置类型。
  obtain ⟨C',U',D',q',data,target⟩ := setup.elastic.elim fun _ table =>
    table.get_l hZFC hκ haω language.limit
  have eq := ZF.v_unique_l I hZF target.rank language.rank
  subst C'
  have eq := hZF.1.eq_of_same_members U' U (fun x => (target.constants x).trans (language.constants x).symm)
  subst U'
  have eq := target.pool.unique_l hZF.1 I language.pool
  subst D'
  obtain ⟨v,drop,elastic⟩ := elastic
  obtain ⟨_,v₀,_,drop₀,prefixType⟩ := full.dcp_l hZF setup.omega setup.two language.pool
  have eq := drop₀.unique_l I hZF.1 drop
  subst v₀
  have elastic' : Tg_elastic_d I p.a p.b D q' u :=
    ⟨v,drop,language.elastic_transfer_l hZFC target setup.omega hκ hY model prefixType elastic⟩
  have heU := (tt_constants_finite_l hZF setup.omega heω language.limit language.rank language.constants).2
  have request : Tg_query_request_d hZF p.ω κ p.e p.e p.A :=
    ⟨language.limit,heω,C,U,language.rank,language.constants,heU,hAU⟩
  obtain ⟨key,row,encoded,entry,d,q₀,N,m,C',U',Du,Dw,pn,pm,pp,pb,ph,t,v₀,
    arity,rowCode,codes,tail,rank,constants,poolU,_,nodeQuery,_,_,_,_⟩ :=
    setup.queries.get_l hZFC setup.limit setup.above setup.rank hκ request
  have zero : Td_arity_d I p.e p.e p.a p.b p.c :=
    ⟨(ZF.ordinalAddition_zero_iff hZF I setup.empty).mpr rfl,setup.one,setup.two,setup.three⟩
  obtain ⟨ed,eq₀,eN,em⟩ := arity.unique_l hZF zero
  subst d q₀ N m
  have eq := ZF.v_unique_l I hZF rank language.rank
  subst C'
  have eq := hZF.1.eq_of_same_members U' U (fun x => (constants x).trans (language.constants x).symm)
  subst U'
  have eq := poolU.unique_l hZF.1 I full.pool
  subst Du
  have queryData : Td_query_data_d p.Q κ p.e p.e p.A C U P Dw pn pm pp pb ph :=
    ⟨key,row,t,v₀,encoded,entry,rowCode,codes,tail⟩
  have groups : Td_groups_d I p.ω p.e p.a r p.e p.e := by
    constructor <;> intro x <;> refine iff_of_false (setup.empty x) ?_ <;>
      rintro ⟨i,hi,ne,_,_⟩ <;>
      exact ((setup.one i).mp hi).elim (setup.empty i) (fun eq => ne (hZF.1.eq_of_same_members i p.e eq))
  have truth := (nodeQuery.2 c Y R r p.δ u p.S model (v_transitive_l I hY) full first).mpr
    ⟨p.e,p.e,full.constants p.e heU,full.constants p.e heU,groups.cover_l,
      (tg_node_empty_l I hZF.1 setup.empty).mpr root,groups⟩
  -- 真实类型和四元走法均位于原 Vδ，供原坍缩枚举实际选取。
  have algebra := sc_v_algebra_l hZFC setup.limit setup.rank
  have hwX := ZF.v_ordinal_mem_l I hZF setup.rank setup.above
  have heX := v_transitive_l I setup.rank p.ω hwX p.e heω
  have hUX := tt_constants_rank_l hZF setup.rank setup.limit hκ language.rank language.constants
  have hPX := full.pool.rank_mem_l (ZF.modelsKP hZF) setup.omega setup.rank setup.limit hwX full.finite hUX
  have sub : M.MemberSubset u P := fun x hx => ((full.truth x).mp hx).1
  obtain ⟨a,ha,move⟩ := sc_quad_l algebra heX heX (ZF.v_ordinal_mem_l I hZF setup.rank hκ)
    (v_subset_mem_l I setup.rank hPX sub)
  refine ⟨κ,C,a,u,above,hκ,language.rank,ha,move,fun n h z digits growth => ?_⟩
  have rest : M.IsRestrictionOf I p.e z p.e := ⟨(tg_graph_empty_l I setup.empty).1.1,
    fun i v => iff_of_false (fun ⟨q,_,hq⟩ => setup.empty q hq) (fun h => setup.empty i h.1)⟩
  exact ⟨p.e,p.e,κ,u,p.e,p.a,p.b,p.c,z,p.e,C,U,P,Dw,pn,pm,pp,pb,ph,C,U,D,
    q'.largest,q'.domain,q'.inaccessible,q'.stretch,move,heω,hκ,zero,digits,rest,request,queryData,
    sub,data,elastic',truth,growth,Or.inl ⟨rfl,μ,Y,c,R,r,hμ,hY,model,full,first,last⟩⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 辅助轮的实际准备状态与合法请求

状态保存实际三阶段时钟、已落下的实数图和前一个请求。由武丁重置构造直接
证明每个这样的状态都有合法请求；不把“存在下一步”加入递归的假设。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Td_ready_d (p : Tg_params_d M.Domain) (X n h : M.Domain) : Prop :=
  M.mem n p.ω ∧ ∃ i z, M.mem i p.ω ∧ Fn0_d i X h ∧ M.IsOrdinalDivision I i p.c n p.e ∧
    Tg_digits_d hZF p.c p.b n p.A h z ∧
    (n = p.e ∨ ∃ j a ℓ k κ u, M.SuccessorOf n j ∧ Tg_event_d I p.c j p.e h a ∧ Td_move_d a ℓ k κ u ∧ M.mem κ p.δ)

def td_ready_m {d} (ω e c b δ A X n h : Term d) : Formula 1 d := set[d] ⟪⌜n⌝ₛ ∈ ⌜ω⌝ₛ ∧
  (∃ i z, i ∈ ⌜ω⌝ₛ ∧ ⌜fn0_m⌝ₚ(i, ⌜X⌝ₛ, ⌜h⌝ₛ) ∧
    ⌜Formula.isOrdinalDivision kpair_convention_l⌝ₚ(i, ⌜c⌝ₛ, ⌜n⌝ₛ, ⌜e⌝ₛ) ∧
    ⌜tg_digits_m⌝ₚ(⌜c⌝ₛ, ⌜b⌝ₛ, ⌜n⌝ₛ, ⌜A⌝ₛ, ⌜h⌝ₛ, z) ∧
    (⌜n⌝ₛ = ⌜e⌝ₛ ∨ (∃ j a ℓ k κ u, ⌜Formula.isSuccessor⌝ₚ(⌜n⌝ₛ, j) ∧
      ⌜tg_event_m⌝ₚ(⌜c⌝ₛ, j, ⌜e⌝ₛ, ⌜h⌝ₛ, a) ∧ ⌜td_move_m⌝ₚ(a, ℓ, k, κ, u) ∧ κ ∈ ⌜δ⌝ₛ)))⟫
derive_free_closed td_ready_m

theorem td_ready_sat_l {d} (ρ : Env M d) (p : Tg_params_d (Term d)) (X n h : Term d) :
    Formula.satisfies ρ (td_ready_m p.ω p.e p.c p.b p.δ p.A X n h) ↔
      Td_ready_d hZF (p.map_l (fun t => t.eval ρ)) (X.eval ρ) (n.eval ρ) (h.eval ρ) := by
  simp only [td_ready_m, Td_ready_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, fn0_sat_l hZF.1, Formula.satisfies_isOrdinalDivision_iff I hZF.1,
    tg_digits_sat_l hZF, Formula.satisfies_disj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1,
    Formula.satisfies_isSuccessor_iff, tg_event_sat_l I hZF.1, td_move_sat_l hZF.1,
    Tg_params_d.map_l, Definitional.Term.eval_weaken]; rfl

/-- 逐步检查实际构造可追加历史，不依赖泛型捕获层或额外合法性判定器。 -/
theorem Td_histories_d.admit_l {p : Tg_params_d M.Domain} {X F L i n h a : M.Domain}
    (histories : Td_histories_d hZF p X F L) (hw : M.IsOmega p.ω) (hi : M.mem i p.ω)
    (hn : M.mem n p.ω) (fn : Fn0_d i X h) (div : M.IsOrdinalDivision I i p.c n p.e)
    (ha : M.mem a X) (aux : Td_aux_d hZF p n h a) : Cg_admit_d hZF p.ω L h a := by
  obtain ⟨j,t,hj,ft,endt⟩ := ZF.fseq_end_exists_l I hZF hw hi (fn0_function_l (ZF.modelsKP hZF) fn) ha
  obtain ⟨j',i',d⟩ := endt
  have ei := d.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fn).2.1
  have ej := d.source.2.2.2.eq hZF.1 ft.2.1
  have succ : M.SuccessorOf j i := ej ▸ ei ▸ d.length_successor
  exact ⟨t,(histories.2 t).mpr ⟨(histories.1 t).mpr ⟨j,hj,ft⟩,
    td_check_end_l hZF hj succ (fn0_of_function_l (ZF.modelsKP hZF) ft) fn ⟨j',i',d⟩
      ⟨n,p.e,hn,div,Or.inl ⟨rfl,aux⟩⟩⟩,j',i',d⟩

variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "K" => kp_pair_l (ZF.modelsKP hZ)

theorem Td_setup_d.ready_empty_l {p : Tg_params_d M.Domain} {X : M.Domain}
    (setup : Td_setup_d hZFC p X) : Td_ready_d hZ p X p.e p.e := by
  have he := num_mem_l hZ.1 setup.omega (show Num_d 0 p.e from setup.empty)
  have oe := setup.omega.members_areOrdinals (ZF.modelsKP hZ) p.e he
  obtain ⟨hc, _⟩ := tg_clock_l hZ setup.omega setup.empty setup.one setup.two setup.three he
  have oc := setup.omega.members_areOrdinals (ZF.modelsKP hZ) p.c hc
  have ec := oc.empty_mem_of_nonempty (ZF.modelsKP hZ) ⟨p.b, setup.three.predecessor_mem⟩ setup.empty
  have empty (Y : M.Domain) : Fn0_d p.e Y p.e := ⟨fun x hx => (setup.empty x hx).elim,
    fun x hx => (setup.empty x hx).elim, fun x hx => (setup.empty x hx).elim⟩
  exact ⟨he, p.e, p.e, he, empty X, ⟨oe, ec, p.e,
    (ZF.ordinalMultiplication_zero_iff hZ K oc setup.empty).mpr setup.empty,
    (ZF.ordinalAddition_zero_iff hZ K setup.empty).mpr rfl⟩,
    ⟨empty p.A, fun i _ hi => (setup.empty i hi).elim⟩, Or.inl rfl⟩

/-- 可继续性来自原重置类型工厂，包括零轮的字母表秩界和后继轮的参数域增长。 -/
theorem Td_setup_d.ready_move_l {p : Tg_params_d M.Domain} {X n h : M.Domain}
    (setup : Td_setup_d hZFC p X) (hd : Woodin_d K p.δ) (root : M.mem p.e p.S)
    (ready : Td_ready_d hZ p X n h) : ∃ a, M.mem a X ∧ Td_aux_d hZ p n h a := by
  obtain ⟨_, i, z, _, _, _, digits, old⟩ := ready
  have heω := num_mem_l hZ.1 setup.omega (show Num_d 0 p.e from setup.empty)
  have zero := setup.limit.1.transitive p.ω setup.above p.e heω
  have bound : ∃ τ, M.mem τ p.δ ∧ (n = p.e ∨ ∃ j a ℓ k u,
      M.SuccessorOf n j ∧ Tg_event_d K p.c j p.e h a ∧ Td_move_d a ℓ k τ u) := by
    rcases old with eq | ⟨j, a, ℓ, k, τ, u, succ, event, data, below⟩
    · exact ⟨p.e, zero, Or.inl eq⟩
    · exact ⟨τ, below, Or.inr ⟨j, a, ℓ, k, u, succ, event, data⟩⟩
  obtain ⟨τ, hτ, old⟩ := bound
  obtain ⟨B, hB, pair⟩ := (sc_v_algebra_l hZFC setup.limit setup.rank).pair p.A τ setup.letters
    (ZF.v_ordinal_mem_l K hZ setup.rank hτ)
  obtain ⟨χ, Z, hχ, hZ', sub⟩ := (ZF.v_unfold_l K hZ setup.rank B).mp hB
  have hAZ := sub p.A ((pair p.A).mpr (Or.inl rfl))
  have hτχ := ZF.v_ordinal_height_l hZ hZ' (setup.limit.1.mem hτ) (sub τ ((pair τ).mpr (Or.inr rfl)))
  obtain ⟨κ, C, a, u, above, _, rank, ha, _, legal⟩ := setup.reset_move_l hZFC hd root hχ
  refine ⟨a, ha, legal n h z digits ?_⟩
  rcases old with eq | ⟨j, v, ℓ, k, u, succ, event, data⟩
  · exact Or.inl ⟨eq, ZF.v_mono_l K hZ hZ' rank ((v_ordinal_l K rank).transitive χ above) p.A hAZ⟩
  · exact Or.inr ⟨j, v, ℓ, k, τ, u, succ, event, data, (v_ordinal_l K rank).transitive χ above τ hτχ⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## demanding 游戏中原 I 策略控制下的三步推进

最小请求合法后，I 的两种应答由原获胜策略的控制集合保证合法；奇数轮读取
对手的原字母。三个实际追加图同时给出下一轮时钟和实数前缀，未引入续步谕示。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}
variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "K" => kp_pair_l (ZF.modelsKP hZ)

theorem Td_ready_d.advance_l {p : Tg_params_d M.Domain} {X F L G J σ R n m h h₁ h₂ t a w y : M.Domain}
    (setup : Td_setup_d hZFC p X) (histories : Td_histories_d hZ p X F L)
    (owner : Tg_owner_d hZ p.ω p.c p.a p.b J) (control : Cg_control_d K true p.ω p.e X F L G J σ R)
    (ready : Td_ready_d hZ p X n h) (hh : M.mem h R) (succ : M.SuccessorOf m n)
    (h₁F : M.mem h₁ F) (h₂F : M.mem h₂ F) (tF : M.mem t F)
    (e₁ : Fseq_end_d K p.ω h₁ h a) (e₂ : Fseq_end_d K p.ω h₂ h₁ w) (e₃ : Fseq_end_d K p.ω t h₂ y)
    (legal : Cg_admit_d hZ p.ω L h a) (value : Rd_entry_d h₁ w σ)
    (digit : ∃ j, Fn0_d j X h₂ ∧ ((M.mem j J ∧ Rd_entry_d h₂ y σ) ∨ (¬ M.mem j J ∧ M.mem y p.A))) :
    M.mem t R ∧ Td_ready_d hZ p X m t ∧ Td_aux_d hZ p n h a ∧ Tg_event_d K p.c n p.e t a ∧
      M.mem y p.A ∧ ∃ j, Fn0_d j X h₂ ∧ M.IsOrdinalDivision K j p.c n p.b ∧
        Td_answer_d hZ p n h₁ w ∧ Tg_event_d K p.c n p.e h₁ a ∧ Tg_event_d K p.c n p.a t w := by
  obtain ⟨hn, i, z, hi, fh, div, digits, _⟩ := ready
  obtain ⟨j₁, hj₁, fh₁⟩ := (histories.1 h₁).mp h₁F
  obtain ⟨j₂, hj₂, fh₂⟩ := (histories.1 h₂).mp h₂F
  obtain ⟨j₃, hj₃, ft⟩ := (histories.1 t).mp tF
  have ends {s t x i j : M.Domain} (fs : Fn0_d i X s) (ft : M.IsSetFunctionFromTo K t j X)
      (en : Fseq_end_d K p.ω t s x) : M.SuccessorOf j i ∧ Rd_entry_d i x t := by
    obtain ⟨a, b, d⟩ := en
    have ei := d.prefix_sequence.2.2.2.eq hZ.1 (fn0_function_l (ZF.modelsKP hZ) fs).2.1
    have ej := d.source.2.2.2.eq hZ.1 ft.2.1
    exact ⟨ej ▸ ei ▸ d.length_successor, ei ▸ d.last_value⟩
  obtain ⟨s₁, v₁⟩ := ends fh fh₁ e₁
  obtain ⟨s₂, v₂⟩ := ends (fn0_of_function_l (ZF.modelsKP hZ) fh₁) fh₂ e₂
  obtain ⟨s₃, v₃⟩ := ends (fn0_of_function_l (ZF.modelsKP hZ) fh₂) ft e₃
  obtain ⟨hc, _⟩ := tg_clock_l hZ setup.omega setup.empty setup.one setup.two setup.three hi
  have oc := setup.omega.members_areOrdinals (ZF.modelsKP hZ) p.c hc
  have ab := oc.transitive p.b setup.three.predecessor_mem p.a setup.two.predecessor_mem
  have div₁ := tg_division_next_l hZ oc div setup.one s₁ ab
  have div₂ := tg_division_next_l hZ oc div₁ setup.two s₂ setup.three.predecessor_mem
  have ne₀ : p.e ≠ p.a := fun eq => setup.empty p.e (eq.symm ▸ setup.one.predecessor_mem)
  have ne₁ : p.e ≠ p.b := fun eq => setup.empty p.a (eq.symm ▸ setup.two.predecessor_mem)
  have turn₀ : ¬ M.mem i J := fun own => ((owner.read_l hZ (setup.omega.isOrdinal (ZF.modelsKP hZ)) oc
    ⟨p.b, setup.three.predecessor_mem⟩ hi hn div).mp own).elim ne₀ (fun h => ne₁ h.1)
  obtain ⟨h₁', check, endt⟩ := legal
  have eq := fseq_end_rebuild_l K hZ.1 endt e₁; subst h₁'
  have h₁R := control.step i h a h₁ hi hh (fh₁.output_mem_of_pairMember v₁) fh e₁ (Or.inl ⟨turn₀, check⟩)
  have turn₁ := (owner.read_l hZ (setup.omega.isOrdinal (ZF.modelsKP hZ)) oc ⟨p.b, setup.three.predecessor_mem⟩ hj₁ hn div₁).mpr (Or.inl rfl)
  have h₂R := control.step j₁ h₁ w h₂ hj₁ h₁R (fh₂.output_mem_of_pairMember v₂)
    (fn0_of_function_l (ZF.modelsKP hZ) fh₁) e₂ (Or.inr ⟨turn₁, value⟩)
  have replyStep := (td_step_read_l hZ (setup.omega.members_areOrdinals (ZF.modelsKP hZ) j₁ hj₁) oc
    ⟨p.b, setup.three.predecessor_mem⟩ hn div₁).mp
    (((histories.2 h₂).mp (control.legal.current_l ((control.positions h₂).mp h₂R).1)).2.end_l hZ
      (fn0_of_function_l (ZF.modelsKP hZ) fh₁) e₂)
  have answer : Td_answer_d hZ p n h₁ w := replyStep.elim (fun h => (ne₀ h.1.symm).elim)
    (fun h => h.elim And.right (fun h => (KP.mem_irrefl_d (ZF.modelsKP hZ) p.a (h.1.symm ▸ setup.two.predecessor_mem)).elim))
  obtain ⟨j, fj, digit⟩ := digit
  have eq := fj.domain_eq_l hZ.1 (fn0_of_function_l (ZF.modelsKP hZ) fh₂); subst j
  have tR : M.mem t R := by
    rcases digit with ⟨own, value⟩ | ⟨own, hy⟩
    · exact control.step j₂ h₂ y t hj₂ h₂R (ft.output_mem_of_pairMember v₃)
        (fn0_of_function_l (ZF.modelsKP hZ) fh₂) e₃ (Or.inr ⟨own, value⟩)
    ·
      have chk := td_check_end_l hZ hj₃ s₃ (fn0_of_function_l (ZF.modelsKP hZ) ft)
        (fn0_of_function_l (ZF.modelsKP hZ) fh₂) e₃ ⟨n, p.b, hn, div₂, Or.inr (Or.inr ⟨rfl, hy⟩)⟩
      exact control.step j₂ h₂ y t hj₂ h₂R (ft.output_mem_of_pairMember v₃)
        (fn0_of_function_l (ZF.modelsKP hZ) fh₂) e₃ (Or.inl ⟨own, (histories.2 t).mpr ⟨tF, chk⟩⟩)
  have step := (td_step_read_l hZ (setup.omega.members_areOrdinals (ZF.modelsKP hZ) j₂ hj₂) oc
    ⟨p.b, setup.three.predecessor_mem⟩ hn div₂).mp
    (((histories.2 t).mp (control.legal.current_l ((control.positions t).mp tR).1)).2.end_l hZ
      (fn0_of_function_l (ZF.modelsKP hZ) fh₂) e₃)
  have be : p.b ≠ p.e := Ne.symm ne₁
  have ba : p.b ≠ p.a := fun eq => KP.mem_irrefl_d (ZF.modelsKP hZ) p.a (eq ▸ setup.two.predecessor_mem)
  have hy := step.elim (fun h => (be h.1).elim) (fun h => h.elim (fun h => (ba h.1).elim) And.right)
  have sub : M.MemberSubset h t := fun x hx => e₃.subset_l K x (e₂.subset_l K x (e₁.subset_l K x hx))
  obtain ⟨z', _, digits'⟩ := digits.append_l hZ setup.omega oc hn succ sub ft.1 hy ⟨j₂, div₂, v₃⟩
  have auxStep := (td_step_read_l hZ (setup.omega.members_areOrdinals (ZF.modelsKP hZ) i hi) oc
    ⟨p.b, setup.three.predecessor_mem⟩ hn div).mp (((histories.2 h₁).mp check).2.end_l hZ fh e₁)
  have aux := auxStep.elim And.right (fun h => h.elim (fun h => (ne₀ h.1).elim) (fun h => (ne₁ h.1).elim))
  have saved := aux
  obtain ⟨ℓ, k, κ, u, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, data, _, hκ, _⟩ := saved
  obtain ⟨m', sm', hm'⟩ := setup.omega.1.2 n hn
  have eq := sm'.eq hZ.1 succ
  exact ⟨tR, ⟨eq ▸ hm', j₃, z', hj₃, fn0_of_function_l (ZF.modelsKP hZ) ft,
    tg_division_cycle_l hZ oc div₂ setup.three succ s₃ setup.empty, digits',
    Or.inr ⟨n, a, ℓ, k, κ, u, succ, (Tg_event_d.end_l (Tg_event_d.end_l ⟨i, div, v₁⟩ e₂) e₃), data, hκ⟩⟩,
    aux, (Tg_event_d.end_l (Tg_event_d.end_l ⟨i, div, v₁⟩ e₂) e₃), hy, j₂,
    fn0_of_function_l (ZF.modelsKP hZ) fh₂, div₂, answer, ⟨i, div, v₁⟩, Tg_event_d.end_l ⟨j₁, div₁, v₂⟩ e₃⟩

end YesMetaZFC.SetTheory.LargeCardinal
