import YesMetaZFC.SetTheory.LargeCardinal.TypeGameStepResult
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRecovery
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRestart
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameRigidRead
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameAnchor
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameQueryTransfer
import YesMetaZFC.SetTheory.LargeCardinal.TypeGameIssuedLow
import YesMetaZFC.SetTheory.LargeCardinal.TypeGamePastStep
import YesMetaZFC.SetTheory.LargeCardinal.TypeImageRead
import YesMetaZFC.SetTheory.LargeCardinal.IterationWorkingApply
import YesMetaZFC.Model.SetTheory.Internal.SubtypeSource
import YesMetaZFC.Model.SetTheory.Internal.EmbeddingRelative
import YesMetaZFC.Model.SetTheory.Internal.SubtypeProgramTransfer

/-! # 继续较早轮的实际跨模型超幂

当前模型中的弹性和超过见证产生 E₂ₙ，施加源是所选较早节点的完整模型。
共同秩段识别旧类型的像，原程序沿实际树根图进入目标；由原子类型查询
自动取得候选的较低层实现。旧回答基底先推出最大序数查询，再在同一目标
反射层恢复恰好一个新标签，并直接形成下一轮输入、回答及实际奇数树边。
当前节点查询和候选由原策略已经发出的走法自动读取，低层参数界由原字母表
所在层推出。旧轮记录、dcp 弹性及任意排列均保留；整列支撑界由实际树的末项推出。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω X η C : M.Domain} (nc : Nonempty {x // M.mem x C}) (ρ : Env (rt_model_l C nc) 28)
local notation "p" => (fun i => Subtype.val (Env.bound ρ i))
local notation "σ" => (Fin.cases (p 21) (Fin.cases (p 22) (Fin.cases (p 23) (Fin.cases (p 24)
  (Fin.cases (p 25) (Fin.cases (p 26) (fun _ => p 27)))))))

theorem Tg_context_d.continue_image_tree_l {c₀ α ξ T J G E H k c d R Y S K K' ζ V η₀ C₀ o π π₀ Cᵣ γ Z₀
    H₀ μᵣ Kₕ Lᵣ Vᵣ qᵣ : M.Domain}
    (context : Tg_context_d ω X η C) (prior : Tg_context_d ω Y η₀ C₀)
    (nc₀ : Nonempty {x // M.mem x C₀}) (ρ₀ : Env (rt_model_l C₀ nc₀) 54)
    (old : Formula.satisfies ρ₀ tg_round0_m) (oldType : (ρ₀.bound 11).val = p 7)
    (oldκ : (ρ₀.bound 15).val = p 1) (oldn : (ρ₀.bound 24).val = p 3) (oldU : (ρ₀.bound 13).val = p 5)
    (owner : Ic_model_d hZF ω (p 1) K X R) (source : Ic_model_d hZF ω (p 1) K' Y S)
    (tree : It_pnice_d hZF ω c₀ α T J G E H) (succ : M.SuccessorOf α ξ)
    (hc : Rd_entry_d ξ c J) (hd : Rd_entry_d k d J) (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (ho : ∀ x, ¬ M.mem x o) (root : It_map_d G o ξ π) (root₀ : It_map_d G o k π₀)
    (iRoot : Rd_entry_d Cᵣ C π) (iRoot₀ : Rd_entry_d Cᵣ C₀ π₀)
    (anchor : Tg_anchor_d γ Z₀ X π) (priorAnchor : Tg_anchor_d γ Z₀ Y π₀) (lower : M.MemberSubset γ (p 1))
    (hγ : M.IsLimitOrdinal γ) (hωZ : M.mem ω Z₀)
    (ι : Env (rt_model_l C nc) 46) (issued : Formula.satisfies ι tg_issued0_m)
    (ne : ι.bound 23 ≠ ι.bound 1)
    (row : Tg_past_at_d H₀ (ι.bound 22).val k Y S μᵣ Kₕ η₀ C₀ Lᵣ Vᵣ qᵣ)
    (code : Tg_saved_code_d ω Vᵣ qᵣ (fun i => (ρ₀.bound i).val))
    (lowS : M.mem (ρ₀.bound 40).val Z₀)
    (oldPlayed : Tg_play_d C (ι.bound 4).val (ι.bound 3).val (ι.bound 20).val (ρ₀.bound 40).val)
    (labelSub : M.MemberSubset (ρ₀.bound 41).val (ι.bound 23).val)
    (links : ∀ i : Fin 6, (ι.bound ([0, 1, 27, 28, 24, 25].get i)).val =
      [ω, (ρ₀.bound 17).val, p 3, p 9, p 8, p 13].get i)
    (codes : ∀ i : Fin 9, p ([14, 16, 21, 22, 23, 24, 25, 26, 27].get i) =
      (ι.bound ([36, 37, 38, 39, 40, 41, 42, 43, 44].get i)).val)
    (letters : M.mem (ι.bound 6).val Z₀)
    (hw : p 0 = ω) (hδ : M.IsLimitOrdinal (p 2)) (regular : Sc_regular_d X (p 2))
    (hV : M.mem V X) (rank : Vr_d X ζ V)
    (hV' : M.mem V Y) (rank' : Vr_d Y ζ V) (hζ : M.IsLimitOrdinal ζ)
    (hVC : M.mem V C₀) (hζδ : M.mem ζ (p 2)) (hκV : M.mem (p 1) V)
    (hU : M.mem (p 5) V) (hD : M.mem (p 6) V) (hu : M.mem (p 7) V)
    (above : ∀ i μ, Rd_entry_d i μ H → M.mem μ (p 8))
    (seed : Formula.satisfies ρ tc_seed0_m) :
    Tg_tree_step_d hZF ω X η c₀ α ξ T J G E c o Cᵣ γ Z₀ H₀ nc ι := by
  obtain ⟨ψ, χ, queries, eqψ, node, queryLow, candidate, eqχ, played⟩ :=
    context.issued_queries_l hZF owner.source nc ι issued (links 0) anchor.member anchor.rank hγ hωZ letters
  have queryRequest := eqψ
  have candidateRequest := eqχ
  have ωψ : (ψ.bound 0).val = ω := (eqψ 0).trans (links 0)
  have eψ : (ψ.bound 1).val = (ρ₀.bound 17).val := (eqψ 1).trans (links 1)
  have lψ : (ψ.bound 2).val = p 3 := (eqψ 2).trans (links 2)
  have nψ : (ψ.bound 3).val = p 9 := (eqψ 3).trans (links 3)
  have node : M.mem (ψ.bound 11).val (p 13) := (show (ι.bound 25).val = p 13 from links 5) ▸ node
  have ωχ : (χ.bound 2).val = ω := (eqχ 2).trans (links 0)
  have τχ : (χ.bound 3).val = p 8 := (eqχ 3).trans (links 4)
  have uχ : (χ.bound 0).val = p 13 := (eqχ 0).trans (links 5)
  have mχ : (χ.bound 1).val = p 9 := (eqχ 1).trans (links 3)
  have fs := (context.read_l hZF owner.source).1
  have facts := seed
  simp only [tc_seed0_m, Formula.satisfies_conj_iff] at facts
  let fp : Fin 12 → Term 28 := fun i => [.bound 0, .bound 3, .bound 14, .bound 15, .bound 16,
    .bound 21, .bound 22, .bound 23, .bound 24, .bound 25, .bound 26, .bound 27].get i
  let ρp := Definitional.Env.substitute ρ fp
  have program : Formula.satisfies ρp ts_program0_m := (Formula.satisfies_bind ρ fp ts_program0_m).mp facts.2.1
  have prog := program
  simp only [ts_program0_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at prog
  have hb : M.mem (p 14) ω := hw ▸ prog.2.1
  have valid := context.continue_l hZF owner.source nc ρ seed
  simp only [tc_result0_m, tc_image_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff] at valid
  obtain ⟨⟨A, K₁, R₁, L, F, a, a', B, S₁, f, κ', U', D', u', core, _, subtype⟩, _, _⟩ := valid
  let ε := ρ.push A |>.push K₁ |>.push R₁ |>.push L |>.push F |>.push a |>.push a' |>.push B
    |>.push S₁ |>.push f |>.push κ' |>.push U' |>.push D' |>.push u'
  let q (t : Term 28) := t.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken
  let t (i : Fin 14) : Term 42 := .bound ⟨i.val, by omega⟩
  obtain ⟨hA, cut, K₂, small, _, hκL, hτL, loc, card, strong, ma, mb, smallUltra, crit, _, _, iU, iD, iu⟩ :=
    ti_image_read_l hZFC nc ε (q (.bound 0)) (q (.bound 1)) (q (.bound 2)) (q (.bound 8))
      (q (.bound 5)) (q (.bound 6)) (q (.bound 7))
      (t 13) (t 12) (t 11) (t 10) (t 9) (t 8) (t 7) (t 6) (t 5) (t 4) (t 3) (t 2) (t 1) (t 0)
      owner.source owner.power context.member context.rank fs (by exact hw) (by exact hδ) (by exact regular) core
  have subtype := ts_subtype_source_l (ZF.modelsKP hZF) fs.transitive nc _ _ _ _ _ _ _ _ _ _ _ _ subtype
  simp only [Definitional.Term.eval_weaken, Definitional.Term.eval_newest] at subtype
  have slots : (fun i : Fin 7 => (Definitional.Term.eval ε
      (Fin.cases (q (.bound 21)) (Fin.cases (q (.bound 22)) (Fin.cases (q (.bound 23))
        (Fin.cases (q (.bound 24)) (Fin.cases (q (.bound 25)) (Fin.cases (q (.bound 26))
          (fun _ => q (.bound 27))))))) i)).val) = σ := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  have subtype' : Ts_subtype_d ω (p 3) κ'.val (p 8) (p 9) U'.val (p 13) (p 14) σ (p 16) u'.val :=
    slots ▸ (hw ▸ subtype)
  have hL := (loc.ordinals_l (ZF.modelsKP hZF) small.transitive).2
  obtain ⟨β, T', J', G', E', H', d', j, N, R', K₀, W, κ₀, next, ext, target, edge, mn, ready,
    ultra, critical, bound, heights, hW, common, level, agreement, same, fixed⟩ :=
    it_working_image_l hZFC tree succ hc hd mx my owner source hA cut hδ small ma mb smallUltra loc strong card
      hκL hV rank hV' rank' hζ hζδ hκV (fun i μ hm => hL.transitive (p 8) hτL μ (above i μ hm))
  have eq := (ultra.elementary_l hZF my.1 mn.1).1.1.1.2 (p 1) κ₀ κ'.val critical.image (same _ _ hκV crit.image)
  subst κ₀
  have hj := ultra.elementary_l hZF my.1 mn.1
  obtain ⟨η', C', iη, iC, context'⟩ := prior.map_l hZF source.source.omega source.source.transitive ready.source.transitive my mn hj
  let nv : Nonempty {x // M.mem x C'} := ⟨⟨ω, context'.omega⟩⟩
  obtain ⟨θ, images, moved⟩ := hj.relative_image_l hZF source.source.omega source.source.transitive
    ready.source.transitive my mn (prior.read_l hZF source.source).1.transitive
    (context'.read_l hZF ready.source).1.transitive nc₀ nv iC tg_round0_m tg_round0_closed_l ρ₀
  have oldImage : Rd_entry_d (p 7) (θ.bound 11).val j := oldType ▸ images 11
  have oldEq := hj.1.1.1.2 (p 7) (θ.bound 11).val u'.val oldImage (same _ _ hu iu)
  have inner x (hx : M.mem x V) := (prior.read_l hZF source.source).1.transitive V hVC x hx
  have inU := (hj.member_l I hZF source.source.omega my mn (same _ _ hU iU) iC).mp (inner _ hU)
  have inD := (hj.member_l I hZF source.source.omega my mn (same _ _ hD iD) iC).mp (inner _ hD)
  have inu := (hj.member_l I hZF source.source.omega my mn (same _ _ hu iu) iC).mp (inner _ hu)
  have relativeSubtype := context'.subtype_l hZF ready.source inU inu hb subtype'
  have data := subtype'
  obtain ⟨_, _, _, query, _⟩ := data
  have inw := (context'.read_l hZF ready.source).1.transitive U'.val inU (p 13) query.1.1
  -- 新语言沿实际树根图传递；共同秩层同时给出所有名字及查询的目标成员性。
  obtain ⟨B₀, R₀, Kᵣ, mb, rootSource⟩ := tree.tree.sources o c₀ (tree.tree.root o ho)
  have jRoot := tree.tree.diagram.elementary o ξ π c₀ B₀ R₀ c X R root (tree.tree.root o ho) hc mb.1 mx.1
  have jPrior := tree.tree.diagram.elementary o k π₀ c₀ B₀ R₀ d Y S root₀ (tree.tree.root o ho) hd mb.1 my.1
  -- 旧回答基底由实际较早轮读取，再沿同一根图送到当前层。
  have fs₀ := (prior.read_l hZF source.source).1
  obtain ⟨oldSeed, oldRound⟩ := (Formula.satisfies_conj_iff ..).mp old
  simp only [tg_seed0_m, Formula.satisfies_rename, tg_seed_m, Formula.satisfies_conj_iff] at oldSeed
  have omega₀ := (Formula.satisfies_isOmega_iff ..).mp oldSeed.1
  let w₀ : (rt_model_l C₀ nc₀).Domain := ⟨ω, prior.omega⟩
  have actualω := rt_omega_l fs₀.transitive nc₀ hZF.1 w₀ source.source.omega
  have eqω := (rt_model_ext_l hZF.1 fs₀.transitive nc₀).eq_of_same_members (ρ₀.bound 16) w₀
    (fun x => ⟨omega₀.2 w₀ actualω.1 x, actualω.2 (ρ₀.bound 16) omega₀.1 x⟩)
  have ω₀ : (ρ₀.bound 16).val = ω := congrArg Subtype.val eqω
  have heω : M.mem (ρ₀.bound 17).val ω := ω₀ ▸ oldSeed.2.2.1
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff] at oldRound
  obtain ⟨_, _, _, _, _, _, _, _, _, replyLanguage, _, _, heightMember, _⟩ := oldRound
  simp only [tg_reply_language_m, Formula.satisfies_bind, tg_reply_language0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at replyLanguage
  obtain ⟨finite₀, _, last₀, _, _, _, _, _, _, _, base₀⟩ := replyLanguage
  let f : Fin 7 → Term 54 := fun i => [.bound 16, .bound 17, .bound 23, .bound 24, .bound 2, .bound 1, .bound 0].get i
  let ε₀ := Definitional.Env.substitute ρ₀ f
  -- 只比较七个参数，避免为核对两次代入而展开整条查询公式。
  simp only [tg_reply_base_m, Formula.satisfies_bind] at base₀
  have base₀ : Formula.satisfies ε₀ tg_reply_base0_m := by
    apply (Formula.closed_env_l tg_reply_base0_m tg_reply_base0_closed_l (ρ := _) (η := ε₀) ?_).mp base₀
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun a => Fin.elim0 a))))))) i
  have zt := priorAnchor.rank.transitive_l hZF source.source.transitive priorAnchor.member
  have hwZ : M.mem ω Z₀ := ωψ ▸ queryLow 0
  have hnω : M.mem (ρ₀.bound 24).val ω := ω₀ ▸ finite₀
  have low₀ : ∀ i : Fin 4, M.mem (ε₀.bound (i.castAdd 3)).val Z₀ := by
    intro i
    exact Fin.cases (ω₀.symm ▸ hwZ) (Fin.cases (zt _ hwZ _ heω)
      (Fin.cases (zt _ hwZ _ (source.source.omega.transitive hZF _ hnω _ last₀))
        (Fin.cases (zt _ hwZ _ hnω) (fun j => Fin.elim0 j)))) i
  obtain ⟨_, ε', eqε, reply'⟩ := priorAnchor.reply_peer_l hZF nc₀ ε₀ anchor nc source.source prior.member fs₀
    rootSource.transitive owner.source.transitive fs.transitive mb my mx jPrior jRoot iRoot₀ iRoot hγ ω₀ low₀ base₀
  have qShape := (Formula.satisfies_conj_iff ..).mp queries |>.2
  have sn := (rt_successor_l fs.transitive nc hZF.1 (ψ.bound 3) (ψ.bound 2)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp qShape.2)
  have cElastic := (Formula.satisfies_conj_iff ..).mp candidate |>.2
  simp only [tg_elastic_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff] at cElastic
  obtain ⟨v, drop, _⟩ := cElastic
  have drop := (td_dcp_source_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) fs.transitive nc fs.pair
    (χ.push v) (.bound 5) (.bound 2) (.bound 8) (.bound 1) (.bound 0)).mp drop
  have mω : M.mem (p 9) ω := hw ▸ ((Formula.satisfies_conj_iff ..).mp (context.continue_l hZF owner.source nc ρ seed)).2.1
  have ℓχ : (ψ.bound 2).val = (χ.bound 4).val := sn.predecessor_eq hZF.1
    ((owner.source.omega.members_areOrdinals hZF _ (nψ.symm ▸ mω)).mem sn.predecessor_mem)
    (Eq.mp (congrArg (fun a => M.SuccessorOf a (χ.bound 4).val) (mχ.trans nψ.symm)) drop.1)
  obtain ⟨_, scope, maximum⟩ := context.rigid_l hZF nc ρ χ ψ ε' owner.source anchor.member anchor.rank lower
    ⟨queryLow 4, queryLow 5, queryLow 6⟩ hw ωχ τχ uχ mχ ωψ ℓχ nψ (eψ.trans (eqε 1).symm)
    ((eqε 0).trans ω₀) ((eqε 3).trans oldn)
    (Eq.mpr ((congrArg (fun a => M.mem a (p 3)) (eqε 2)).trans
      (congrArg (fun a => M.mem (ρ₀.bound 23).val a) oldn.symm)) last₀)
    (Eq.mpr (congrArg (fun a => M.mem a (p 7)) (eqε 6)) (oldType ▸ heightMember)) seed candidate queries reply'
  obtain ⟨π', root'⟩ := next.tree.diagram.map_l hZF (next.tree.diagram.order.root_l hZF ho α ext.1.predecessor_mem)
  have kRoot := next.tree.diagram.elementary o α π' c₀ B₀ R₀ d' N R' root'
    (next.tree.root o ho) target mb.1 mn.1
  have oldRoot := (ext.2.2.2.1 o k π₀ ((tree.tree.diagram.model_domain k).mpr ⟨d, hd⟩)).mpr root₀
  have iRoot' := next.tree.diagram.comp o k α π₀ j π' oldRoot edge root' Cᵣ C₀ C' iRoot₀ iC
  have hLimit := card.limit_l (ZF.modelsKP hZF) small.transitive small.theory.algebra.pair
  have fixedCopy := fixed
  obtain ⟨V₀, hV₀, rank₀, _, _, pointwise⟩ := fixedCopy
  have anchor' := priorAnchor.extend_l hZF owner.source.transitive source.source.transitive ready.source.transitive
    anchor.member anchor.rank hW common level.member level.hierarchy hLimit hκL lower
    hV₀ rank₀ pointwise next.tree.diagram oldRoot edge root'
  have fixedZ z (hz : M.mem z Z₀) : Rd_entry_d z z j := by
    obtain ⟨z', _, iz⟩ := hj.1.1.2.2 z (source.source.transitive Z₀ priorAnchor.member z hz)
    have eq := kRoot.1.1.1.2 z z' z (next.tree.diagram.comp o k α π₀ j π' oldRoot edge root'
      z z z' (priorAnchor.fixed z hz) iz) (anchor'.fixed z hz)
    exact eq ▸ iz
  have lowT : M.mem (ρ₀.bound 41).val Z₀ := priorAnchor.rank.subset_mem_l source.source.transitive
    priorAnchor.member (queryRequest 5 ▸ queryLow 6)
    (source.source.transitive C₀ prior.member _ (ρ₀.bound 41).property) labelSub
  obtain ⟨allQueries, ψ', eqψ, movedψ⟩ := anchor.query_peer_l hZF nc ψ anchor' nv owner.source context.member fs
    rootSource.transitive ready.source.transitive (context'.read_l hZF ready.source).1.transitive mb mx mn jRoot kRoot
    iRoot iRoot' hγ ωψ queryLow queries
  have carried := ts_program_peer_l hZF nc ρp owner.source.omega rootSource.transitive owner.source.transitive
    ready.source.transitive mb mx mn jRoot kRoot rootSource.omega_mem iRoot iRoot' fs.transitive
    (context'.read_l hZF ready.source).1.transitive context'.omega hw program
  have σeq : (fun i : Fin 7 => [p 21, p 22, p 23, p 24, p 25, p 26, p 27].get i) = σ := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))))))) i
  have program' : Ts_program_in_d ω (p 3) (p 14) (p 16) σ C' := σeq ▸ carried
  have hκC' := (hj.member_l I hZF source.source.omega my mn critical.image iC).mp (inner _ hκV)
  have hLC' := context'.rank.subset_mem_l ready.source.transitive context'.member hκC' ready.source.cardinal_mem bound
  have hWC' := (context'.rank.rank_l hZF ready.source.transitive context'.member context'.limit
    hLC' level.member level.hierarchy).1
  have κW := common.ordinal_subset_l hZF owner.source.transitive hW (p 1) hκL
  have ωW := common.subset_mem_l owner.source.transitive hW κW owner.source.omega_mem owner.source.below
  have τW := common.ordinal_subset_l hZF owner.source.transitive hW (p 8) hτL
  obtain ⟨hmω, low, nχ, χ', eqχ, movedχ⟩ := context.candidate_peer_l hZF nc χ context' owner.source ready.source
    rootSource.transitive mb mx mn jRoot kRoot rootSource.omega_mem iRoot iRoot'
    hW common level.member level.hierarchy hLimit
    ωW (Eq.mpr (congrArg (fun a => M.mem a W) τχ) τW) hWC' ωχ
    (Eq.mpr (congrArg (fun a => M.mem a C') uχ) inw) candidate
  have natural := hj.natural_l hZF source.source.omega source.source.transitive ready.source.transitive my mn source.source.omega_mem
  have nImage : Rd_entry_d (p 3) (θ.bound 24).val j := oldn ▸ images 24
  have κImage : Rd_entry_d (p 1) (θ.bound 15).val j := oldκ ▸ images 15
  have UImage : Rd_entry_d (p 5) (θ.bound 13).val j := oldU ▸ images 13
  have eqn := hj.1.1.1.2 (p 3) (θ.bound 24).val (p 3) nImage (natural _ (hw ▸ prog.1))
  have eqκ := hj.1.1.1.2 (p 1) (θ.bound 15).val κ'.val κImage critical.image
  have eqU := hj.1.1.1.2 (p 5) (θ.bound 13).val U'.val UImage (same _ _ hU iU)
  have realized := context'.realize_l hZF nv θ χ' ready.source (moved.mp old) movedχ eqn eqκ eqU oldEq
    ((eqχ 3).trans τχ) ((eqχ 1).trans mχ) ((eqχ 0).trans uχ)
    (Eq.mp (congrArg (fun a => M.mem a ω) mχ) hmω) program' relativeSubtype
  obtain ⟨P, ν, pool, below, witness⟩ := realized
  -- 同一候选的低层实现、最大序数查询及原节点在目标层合流，保留原排列。
  have eqe := hj.1.1.1.2 (ρ₀.bound 17).val (θ.bound 17).val (ρ₀.bound 17).val (images 17) (natural _ heω)
  have candidateDomain := (Formula.satisfies_conj_iff ..).mp candidate |>.1
  simp only [Formula.satisfies_rename, ee_language0_m, ee_domain_pack_m,
    Formula.satisfies_bind, ee_domain_pack0_m, Formula.satisfies_conj_iff] at candidateDomain
  have hωU : M.mem ω (χ.bound 6).val := ωχ ▸ (show M.mem (χ.bound 2).val (χ.bound 6).val from candidateDomain.1.1)
  have witness' : Tg_realized_in_d ω (θ.bound 18).val (θ.bound 24).val (θ.bound 29).val
      (ψ'.bound 3).val (χ'.bound 6).val P (p 13) ν C' := by
    apply Eq.mpr (congrArg (fun n : M.Domain => Tg_realized_in_d ω (θ.bound 18).val n (θ.bound 29).val
      (ψ'.bound 3).val (χ'.bound 6).val P (p 13) ν C') eqn)
    exact Eq.mpr (congrArg (fun m : M.Domain => Tg_realized_in_d ω (θ.bound 18).val (p 3) (θ.bound 29).val m
      (χ'.bound 6).val P (p 13) ν C') ((eqψ 3).trans nψ)) witness
  obtain ⟨εr, eqr, recovered⟩ := context'.recover_l hZF nv θ ψ' ready.source (moved.mp old) movedψ
    ((eqψ 0).trans ωψ) ((eqψ 1).trans (eψ.trans eqe.symm)) ((eqψ 2).trans (lψ.trans eqn.symm))
    (Eq.mpr (congrArg (fun a => M.mem ω a) (eqχ 6)) hωU)
    ⟨Eq.mpr (congr (congrArg M.mem (eqψ 4)) (eqχ 6)) scope.1,
      Eq.mpr (congr (congrArg M.mem (eqψ 5)) (eqχ 6)) scope.2.1,
      Eq.mpr (congr (congrArg M.mem (eqψ 6)) (eqχ 6)) scope.2.2⟩
    (Eq.mpr (congrArg (fun a => M.mem a (p 13)) (eqψ 11)) node)
    (Eq.mpr (congrArg (fun a => M.mem a (p 13)) (eqψ 8)) maximum) witness'
  have imageω := hj.omega_l I hZF source.source.omega source.source.transitive ready.source.transitive my mn source.source.omega_mem
  have ωθ := hj.1.1.1.2 ω (θ.bound 16).val ω (ω₀ ▸ images 16) imageω
  have hlχ := (eqχ 4).trans (ℓχ.symm.trans (lψ.trans eqn.symm))
  have hnχ := ((eqψ 3).trans nψ).trans ((eqχ 1).trans mχ).symm
  have sameRecovery : ∀ i : Fin 10, εr.bound ([7, 8, 10, 11, 12, 13, 23, 24, 25, 28].get i) =
      [θ.bound 16, θ.bound 17, θ.bound 23, θ.bound 24, χ'.bound 1, χ'.bound 6,
        θ.bound 18, θ.bound 19, θ.bound 20, χ'.bound 0].get i := by
    intro i
    apply Subtype.ext
    exact Fin.cases ((eqr 0).trans ωθ.symm) (Fin.cases (eqr 1) (Fin.cases (eqr 3)
      (Fin.cases (eqr 4) (Fin.cases ((eqr 5).trans hnχ) (Fin.cases (eqr 6)
        (Fin.cases (eqr 16) (Fin.cases (eqr 17) (Fin.cases (eqr 18)
          (Fin.cases ((eqr 21).trans ((eqχ 0).trans uχ).symm) (fun j => Fin.elim0 j)))))))))) i
  have belowχ : M.mem (χ'.bound 3).val (θ.bound 15).val :=
    Eq.mpr (congr (congrArg M.mem ((eqχ 3).trans τχ)) eqκ) (bound _ hτL)
  have programθ : Ts_program_in_d ω (θ.bound 24).val (p 14) (p 16) σ C' :=
    Eq.mpr (congrArg (fun n : M.Domain => Ts_program_in_d ω n (p 14) (p 16) σ C') eqn) program'
  have restarted := context'.restart_l hZF ready.source nv θ χ' εr (moved.mp old) movedχ recovered sameRecovery
    (Subtype.ext (((eqχ 2).trans ωχ).trans ωθ.symm)) (Subtype.ext hlχ) ωθ belowχ programθ
  obtain ⟨πp, eqp, v₂, seed₂, a₂, round₂⟩ := restarted
  let ρ₂ := tg_round_env_d (tg_restart_env_d θ χ' εr πp v₂) a₂
  -- 恢复图的包含与真实有限函数域，给出沿同一奇数边恰好增加一个点。
  have ft := (context'.read_l hZF ready.source).1
  have os := (Formula.satisfies_conj_iff ..).mp (moved.mp old) |>.1
  simp only [tg_seed0_m, Formula.satisfies_rename, tg_seed_m, Formula.satisfies_conj_iff] at os
  obtain ⟨_, _, _, _, _, _, _, oldSucc, _, _, _, _, _, _, _, _, _, _, _, oldNode, _⟩ := os
  have oldNode := (tg_node_source_l ft.transitive nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) _ _ _ _ _ _).mp oldNode
  have oldGraph := oldNode.2.2.1
  have nr := recovered
  simp only [tc_recovered0_m, tc_recovered_m, Formula.satisfies_conj_iff] at nr
  obtain ⟨_, _, _, _, _, _, _, _, _, newNode, _, keep⟩ := nr
  have newNode := (tg_node_source_l ft.transitive nv hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) _ _ _ _ _ _).mp newNode
  have newGraph := newNode.2.2.1
  have hs := (rt_successor_l ft.transitive nv hZF.1 (θ.bound 23) (θ.bound 22)).mp
    ((Formula.satisfies_isSuccessor_iff ..).mp oldSucc)
  have en : (εr.bound 10).val = (θ.bound 23).val := eqr 3
  have newGraph : Tg_graph_d I (θ.bound 23).val (εr.bound 2).val := en ▸ newGraph
  have sub : M.MemberSubset (θ.bound 42).val (εr.bound 2).val := by
    intro r hr
    have hr' : M.mem r (εr.bound 26).val := (eqr 19).symm ▸ hr
    let x : (rt_model_l C' nv).Domain := ⟨r, ft.transitive _ (εr.bound 26).property r hr'⟩
    exact (Formula.satisfies_iff_iff ..).mp ((Formula.satisfies_forall_iff ..).mp keep x) |>.mpr
      ((Formula.satisfies_disj_iff ..).mpr (Or.inl hr'))
  obtain ⟨z, hz, push⟩ := tg_graph_extend_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hs oldGraph newGraph sub
  have digits : (ρ₂.bound 40).val = (ψ.bound 5).val := (eqr 8).trans (eqψ 5)
  have oldDigits := hj.1.1.1.2 _ _ _ (images 40) (fixedZ _ lowS)
  have gs : Tg_graph_d I (θ.bound 22).val (ρ₀.bound 40).val := oldDigits ▸ oldNode.1
  have gt : Tg_graph_d I (θ.bound 23).val (ρ₂.bound 40).val := en ▸ newNode.1
  have played' : Tg_play_d C (ι.bound 4).val (ι.bound 3).val (ι.bound 20).val (ρ₂.bound 40).val := by
    rw [digits]; exact played
  have digitSub := oldPlayed.subset_l hZF fs.transitive nc (rt_pair_l fs.transitive nc hZF.1 fs.pair) ι issued
    played' gs gt (fun x hx => (hs x).mpr (Or.inl hx))
  have odd : Tg_odd_d ω H₀ ξ α k G' (ι.bound 1).val (ι.bound 23).val (ι.bound 22).val (ι.bound 7).val
      (ρ₂.bound 19).val (ρ₂.bound 22).val (ρ₂.bound 40).val (ρ₂.bound 42).val :=
    Or.inr ⟨fun eq => ne (Subtype.ext eq), Y, S, μᵣ, Kₕ, η₀, C₀, Lᵣ, Vᵣ, qᵣ,
      (ρ₀.bound 19).val, (ρ₀.bound 22).val, (ρ₀.bound 40).val, (ρ₀.bound 41).val, (ρ₀.bound 42).val, j, (θ.bound 42).val, (θ.bound 22).val, z,
      row, ⟨_, code, rfl, rfl, rfl, rfl, rfl⟩, edge, images 19, images 22, images 42, hs, hz, push,
      fixedZ _ lowS, digitSub, fixedZ _ lowT, labelSub⟩
  have nextSeed := seed₂
  simp only [tg_seed0_m, tg_seed_m, Formula.satisfies_conj_iff] at nextSeed
  have first := (rt_successor_l (context'.read_l hZF ready.source).1.transitive nv hZF.1
    (ρ₂.bound 23) (ρ₂.bound 22)).mp ((Formula.satisfies_isSuccessor_iff ..).mp nextSeed.2.2.2.2.2.2.2.1)
  have state := (tg_issued_sat_l (rt_pair_l fs.transitive nc hZF.1 fs.pair)
    (rt_model_ext_l hZF.1 fs.transitive nc) ι).mp issued
  have first' := (rt_successor_l fs.transitive nc hZF.1 (ι.bound 27) (ι.bound 26)).mp state.first
  have el : (ρ₂.bound 23).val = (ι.bound 27).val := eqn.trans (links 2).symm
  have ek := first.predecessor_eq hZF.1
    ((ready.source.omega.members_areOrdinals hZF _ (eqn.symm ▸ (hw ▸ prog.1))).mem first.predecessor_mem)
    (el.symm ▸ first')
  have request : Tg_request_d (fun i => (ι.bound i).val) (fun i => (ρ₂.bound i).val) := by
    intro i
    exact Fin.cases (ωθ.trans (links 0).symm) (Fin.cases (eqe.trans (links 1).symm)
      (Fin.cases ek (Fin.cases el (Fin.cases ((eqχ 1).trans (candidateRequest 1))
        (Fin.cases ((eqp 2).trans (codes 0)) (Fin.cases ((eqp 3).trans (codes 1))
          (Fin.cases ((eqp 4).trans (codes 2)) (Fin.cases ((eqp 5).trans (codes 3))
            (Fin.cases ((eqp 6).trans (codes 4)) (Fin.cases ((eqp 7).trans (codes 5))
              (Fin.cases ((eqp 8).trans (codes 6)) (Fin.cases ((eqp 9).trans (codes 7))
                (Fin.cases ((eqp 10).trans (codes 8)) (Fin.cases ((eqχ 3).trans (candidateRequest 3))
                  (Fin.cases ((eqχ 6).trans (candidateRequest 6)) (Fin.cases ((eqχ 7).trans (candidateRequest 7))
                    (Fin.cases ((eqχ 0).trans (candidateRequest 0))
                      (Fin.cases ((eqr 9).trans ((eqψ 6).trans (queryRequest 5)))
                        (fun j => Fin.elim0 j))))))))))))))))))) i
  -- 偶数操作的末项界正是新轮下界；奇数操作的施加源仍为原偶数模型 X。
  have above₂ : ∀ i μ, Rd_entry_d i μ H' → M.mem μ (ρ₂.bound 39).val ∨ μ = (ρ₂.bound 39).val := by
    change ∀ i μ, Rd_entry_d i μ H' → M.mem μ (θ.bound 15).val ∨ μ = (θ.bound 15).val
    rw [eqκ]
    exact heights
  have hδ₂ := (context'.round_regular_l hZF nv ρ₂ ready ωθ round₂).1
  have oldData := (Formula.satisfies_conj_iff ..).mp (moved.mp old) |>.2
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff] at oldData
  have hLδ₂ : M.mem L.val (ρ₂.bound 18).val := ordinal_down_l (ZF.modelsKP hZF) hLimit.1 hδ₂.1
    (fun x hx => Eq.mpr (congrArg (fun z => M.mem x z) eqκ) (bound x hx)) oldData.2.2.1
  have hκW₂ : M.mem (ρ₂.bound 21).val W := Eq.mpr (congrArg (fun z => M.mem z W) ((eqχ 3).trans τχ))
    (common.ordinal_subset_l hZF owner.source.transitive hW (p 8) hτL)
  have hWCX := (context.rank.rank_l hZF owner.source.transitive context.member context.limit L.property hW common).1
  have evenNode := ext.2.2.1 ξ c hc
  obtain ⟨β₂, T₂, J₂, G₂, E₂, H₂, c₂, j₂, N₂, R₂, K₂, L₂, F₂, κ₂, U₂, D₂, u₂, η₂, C₂, W₂,
    next₂, ext₂, target₂, edge₂, mn₂, ready₂, ultra₂, critical₂, limit₂, bound₂, subset₂, heights₂,
    iU₂, iD₂, iu₂, reply₂, iη₂, iC₂, context₂, legal₂, hW₂, hWC₂, common₂, level₂, hQ₂, hw₂, agreement₂, fixed₂⟩ :=
    context'.round_l hZFC nv ρ₂ context ready owner next ext.1 target evenNode mn mx
      level.member level.hierarchy hW common hLimit hWCX hLδ₂ hκW₂ ωθ above₂ round₂
  -- 根图按实际树的复合律延伸；旧字母表仍严格低于新临界点。
  obtain ⟨π₂, root₂⟩ := next₂.tree.diagram.map_l hZF
    (next₂.tree.diagram.order.root_l hZF ho β ext₂.1.predecessor_mem)
  have oldEvenRoot := (ext.2.2.2.1 o ξ π succ.predecessor_mem).mpr root
  have oldRoot₂ := (ext₂.2.2.2.1 o ξ π ((next.tree.diagram.model_domain ξ).mpr ⟨c, evenNode⟩)).mpr oldEvenRoot
  have iRoot₂ := next₂.tree.diagram.comp o ξ β π j₂ π₂ oldRoot₂ edge₂ root₂ Cᵣ C C₂ iRoot iC₂
  obtain ⟨_, _, _, hτ, _, _, _, _, exceeds⟩ := facts
  have hτ := (rt_limit_l fs.transitive nc (ZF.modelsKP hZF) (ρ.bound 8)).mp
    ((Formula.satisfies_isLimitOrdinal_iff ..).mp hτ)
  simp only [tx_exceeds_m, Formula.satisfies_bind, tx_exceeds0_m,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at exceeds
  have lower₂ : M.MemberSubset γ (ρ₂.bound 21).val := by
    exact Eq.mpr (congrArg (fun z => M.MemberSubset γ z) ((eqχ 3).trans τχ))
      (fun x hx => hτ.1.transitive (p 1) exceeds.1 x (lower x hx))
  have roundData := (Formula.satisfies_conj_iff ..).mp round₂ |>.2
  simp only [tg_witness0_m, tg_round_m, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff] at roundData
  have hκL₂ := limit₂.1.transitive (ρ₂.bound 15).val bound₂ (ρ₂.bound 21).val roundData.2.1
  have fixedCopy₂ := fixed₂
  obtain ⟨V₂, hV₂, rank₂, _, _, pointwise₂⟩ := fixedCopy₂
  have anchor₂ := anchor.extend_l hZF ready.source.transitive owner.source.transitive ready₂.source.transitive
    anchor'.member anchor'.rank hW₂ common₂ level₂.member level₂.hierarchy limit₂ hκL₂ lower₂
    hV₂ rank₂ pointwise₂ next₂.tree.diagram oldRoot₂ edge₂ root₂
  have κθ : M.MemberSubset (ρ₂.bound 21).val L.val := by
    change M.MemberSubset (χ'.bound 3).val L.val
    rw [(eqχ 3).trans τχ]
    exact hLimit.1.transitive _ hτL
  have past := context'.past_update_l hZF ready nv ρ₂ round₂ ωθ owner.source.transitive hW common
    level.member level.hierarchy hLimit κθ limit₂ hWC₂ common₂ bound₂ hw₂ (limit₂.1.transitive _ hκL₂)
    ready₂.source.transitive level₂.member level₂.hierarchy subset₂ hV₂ rank₂ pointwise₂
    (fun i d hi => ext₂.2.2.1 i d (ext.2.2.1 i d hi)) (ext₂.2.2.1 α d' target) mn
  have high : M.MemberSubset γ (ρ₂.bound 15).val := fun x hx =>
    (limit₂.1.mem bound₂).transitive _ roundData.2.1 x (lower₂ x hx)
  have eκ : (ρ₂.bound 21).val = (ι.bound 24).val := request 14
  have eU : (ρ₂.bound 31).val = (ι.bound 30).val := request 15
  have eD : (ρ₂.bound 32).val = (ι.bound 31).val := request 16
  have eu : (ρ₂.bound 34).val = (ι.bound 25).val := request 17
  exact ⟨k, β, T', J', G', E', H', d', N, R', L.val, K₀, η', C', π',
    next, ext, target, mn, ready, context', root', iRoot', anchor', nv, ρ₂, round₂, request, high, odd,
    ⟨by change M.mem (ρ₂.bound 40).val Z₀; rw [digits]; exact queryLow 5,
      by change Tg_play_d C (ι.bound 4).val (ι.bound 3).val (ι.bound 20).val (ρ₂.bound 40).val; rw [digits]; exact played⟩,
    β₂, T₂, J₂, G₂, E₂, H₂, c₂, j₂, N₂, R₂, K₂, L₂, F₂, κ₂, U₂, D₂, u₂, η₂, C₂, W₂,
    π₂, next₂, ext₂, target₂, edge₂, mn₂, ready₂, eκ ▸ ultra₂, eκ ▸ critical₂, limit₂, bound₂, subset₂, heights₂,
    eU ▸ iU₂, eD ▸ iD₂, eu ▸ iu₂, reply₂, iη₂, iC₂, context₂, hW₂, common₂, level₂,
    root₂, iRoot₂, anchor₂, eκ ▸ past⟩

end YesMetaZFC.SetTheory.LargeCardinal
