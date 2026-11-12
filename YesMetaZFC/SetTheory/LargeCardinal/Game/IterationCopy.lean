import YesMetaZFC.SetTheory.LargeCardinal.Game.PreparedResult
import YesMetaZFC.SetTheory.LargeCardinal.Game.IterationStep
import YesMetaZFC.SetTheory.LargeCardinal.Game.SavedCopy
import YesMetaZFC.SetTheory.LargeCardinal.Game.RoundParity
import YesMetaZFC.SetTheory.LargeCardinal.Game.ResetNative
import YesMetaZFC.SetTheory.LargeCardinal.Game.IterationReset
import YesMetaZFC.SetTheory.LargeCardinal.Game.IterationNextSyntax
import YesMetaZFC.Model.SetTheory.ClassResponse
import YesMetaZFC.SetTheory.Descriptive.Demand.InputIteration
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.FrameUnion
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyOriginalResult
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyTree
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.CopyNice

/-! # 选中旧档案后的两次复制与下一有限状态

所选旧行、准备记录、第一次复制及第二次复制依次给出同一组见证。
两次复制列的包含关系复合，随后在这份实际回答上执行给定原输入。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_prepared_d.iteration_l
    {ω c₀ X₀ R₀ o C₀ S₀ γ Bγ A x : M.Domain} {v : Fin 29 → M.Domain} {a : Fin 46 → M.Domain}
    {old : Tg_archive_row_d M.Domain} (h : Tg_iteration_d hZF ω c₀ o C₀ S₀ γ Bγ A v a)
    (hN : (smdl_structure_l I (R := v 1) h.model.2.1).Models KP)
    (nc : Nonempty {x : (smdl_structure_l I (R := v 1) h.model.2.1).Domain //
      (smdl_structure_l I (R := v 1) h.model.2.1).mem x ⟨v 5,h.request.context.member⟩})
    (ι : Env (rt_model_l (M := smdl_structure_l I (R := v 1) h.model.2.1)
      ⟨v 5,h.request.context.member⟩ nc) 46) (eq : ∀ i, (ι.bound i).val.val = a i)
    (prepared : Tg_prepared_d hZF ω (v 8) (v 11) (v 6) (v 22) (v 23) c₀ X₀ R₀
      (v 0) (v 1) (v 18) (v 19) (v 15) (v 16) C₀ S₀ (v 2) (v 4) (v 5) (v 3) (v 14) γ Bγ
      old.i old.c old.X old.R old.w old.η old.C old.L old.U old.q old.p old.A old.π o (v 7)
      (v 9) (v 10) (v 12) (v 20) h.model hN h.request.context nc ι h.tree.omega)
    (choice : a 23 ≠ a 1 ∧ ∃ l r, M.mem l (v 27) ∧ M.PairMember I l (a 22) (v 3) ∧
      M.PairMember I l r (v 13) ∧ Rt_tuple_d old.values_d r)
    (letters : M.mem A Bγ) (hx : M.mem x A) :
    ∃ w b, Tg_iteration_d hZF ω c₀ o C₀ S₀ γ Bγ A w b ∧ Tg_iteration_next_d hZF ω c₀ x v w a b := by
  have low : M.PairMember I (v 14) (ι.bound 24).val.val (v 1) :=
    Eq.mpr (congrArg (fun z => M.PairMember I (v 14) z (v 1)) (eq 24)) h.request.below
  exact prepared.elim fun p rest => rest.elim fun old_code rest => rest.elim fun _ rest => rest.elim fun l₀ rest =>
    rest.elim fun φ rest => rest.elim fun V rest => rest.elim fun Γ rest => rest.elim fun t rest =>
    rest.elim fun same rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun D rest =>
    rest.elim fun k rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
    rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun nd rest =>
    rest.elim fun θ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
    rest.elim fun _ rest => rest.elim fun y rest => rest.elim fun _ rest => rest.elim fun _ rest =>
    rest.elim fun ζ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
    rest.elim fun _ rest => rest.elim fun ε rest => rest.elim fun _ rest => rest.elim fun _ rest =>
    rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
    rest.elim fun _ rest => rest.elim fun ν rest => rest.elim fun _ rest => rest.elim fun _ rest =>
    rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun new_eq rest =>
    rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun αc rest =>
    rest.elim fun βc rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
    rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
    rest.elim fun Xc rest => rest.elim fun Kc rest => rest.elim fun jc rest => rest.elim fun Lc rest =>
    rest.elim fun Fc rest => rest.elim fun ec rest => rest.elim fun Ls rest => rest.elim fun Js rest =>
    rest.elim fun Os rest => rest.elim fun Zs rest => rest.elim fun Ds rest => rest.elim fun ps rest =>
    rest.elim fun Vs rest => rest.elim fun Ws rest => rest.elim fun qs rest => rest.elim fun d₁ rest =>
    rest.elim fun N₁ rest => rest.elim fun R₁ rest => rest.elim fun j₁ rest => rest.elim fun q₁ rest =>
    rest.elim fun p₁ rest => rest.elim fun D₁ rest => rest.elim fun t₁ rest => rest.elim fun w₁ rest =>
    rest.elim fun η₁ rest => rest.elim fun C₁ rest => rest.elim fun restored rest => rest.elim fun nc₁ rest =>
    rest.elim fun ρ₁ rest => rest.elim fun θ₁ rest => rest.elim fun record_points copied => by
      exact copied.elim fun θ₂ rest => rest.elim fun T₁ rest => rest.elim fun Q₁ rest => rest.elim fun G₁ rest =>
        rest.elim fun E₁ rest => rest.elim fun Λ₁ rest => rest.elim fun H₁ rest => rest.elim fun ST₁ rest =>
        rest.elim fun QT₁ rest => rest.elim fun GT₁ rest => rest.elim fun Y₁ rest => rest.elim fun u₁ rest =>
        rest.elim fun B₁ rest => rest.elim fun β₁ rest => rest.elim fun σ₁ rest => rest.elim fun χ₁ rest =>
        rest.elim fun κ₁ rest => rest.elim fun w₂ rest => rest.elim fun η₂ rest => rest.elim fun C₂ rest =>
        rest.elim fun δ₂ rest => rest.elim fun r₂ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
        rest.elim fun mid rest => rest.elim fun first rest => rest.elim fun _ rest => rest.elim fun _ rest =>
        rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun edge₁ rest => rest.elim fun _ rest =>
        rest.elim fun _ rest => rest.elim fun history₁ rest => rest.elim fun rows₁ rest =>
        rest.elim fun codes₁ rest => rest.elim fun maps₁ rest => rest.elim fun _ tail => by
          exact tail.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
            rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
            rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
            rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
            rest.elim fun φ₁ rest => rest.elim fun U₁ rest => rest.elim fun V₂ rest => rest.elim fun Γ₁ rest =>
            rest.elim fun k₁ rest => rest.elim fun adjacent rest => rest.elim fun _ rest => rest.elim fun _ rest =>
            rest.elim fun model₁ rest => rest.elim fun context₁ rest => rest.elim fun nc₂ rest =>
            rest.elim fun ε₂ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
            rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun ψ rest => rest.elim fun ζ₂ rest =>
            rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
            rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
            rest.elim fun W rest => rest.elim fun ν₂ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
            rest.elim fun _ rest => rest.elim fun εr rest => rest.elim fun _ rest => rest.elim fun _ rest =>
            rest.elim fun ρr rest => rest.elim fun old_eq rest => rest.elim fun _ rest => rest.elim fun πp rest =>
            rest.elim fun _ rest => rest.elim fun x₂ rest => rest.elim fun _ rest => rest.elim fun a₂ rest =>
            rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun Lr rest => rest.elim fun Wr rest =>
            rest.elim fun qr rest => rest.elim fun _ rest => rest.elim fun new_code rest =>
            rest.elim fun restart_link rest => rest.elim fun _ rest =>
            rest.elim fun X₂ rest => rest.elim fun K₂ rest => rest.elim fun R₂ rest => rest.elim fun F₂ rest =>
            rest.elim fun c₂ rest => rest.elim fun d₂ rest => rest.elim fun Y₂ rest => rest.elim fun S₂ rest =>
            rest.elim fun j₂ rest => rest.elim fun κ₂ rest => rest.elim fun U₂ rest => rest.elim fun D₂ rest =>
            rest.elim fun u₂ rest => rest.elim fun _ rest => rest.elim fun α₂ rest => rest.elim fun β₂ rest =>
            rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
            rest.elim fun _ rest => rest.elim fun Γ₂ rest => rest.elim fun k₂ rest => rest.elim fun z₂ rest =>
            rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
            rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun Ls₂ rest =>
            rest.elim fun Js₂ rest => rest.elim fun Os₂ rest => rest.elim fun Zs₂ rest => rest.elim fun Ds₂ rest =>
            rest.elim fun ps₂ rest => rest.elim fun Vs₂ rest => rest.elim fun Ws₂ rest => rest.elim fun qs₂ rest =>
            rest.elim fun d₃ rest => rest.elim fun P₃ rest => rest.elim fun R₃ rest => rest.elim fun j₃ rest =>
            rest.elim fun q₃ rest => rest.elim fun p₃ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
            rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ tail => by
              exact tail.elim fun θ₃ rest => rest.elim fun T₃ rest => rest.elim fun Q₃ rest =>
                rest.elim fun G₃ rest => rest.elim fun E₃ rest => rest.elim fun Λ₃ rest => rest.elim fun tree₃ rest =>
                rest.elim fun second rest => rest.elim fun qn₃ rest => rest.elim fun edge₃ rest =>
                rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
                rest.elim fun critical rest => rest.elim fun lf₃ rest => rest.elim fun levels₃ rest =>
                rest.elim fun _ rest => rest.elim fun A₃ rest => rest.elim fun Qp₃ rest => rest.elim fun Bp₃ rest =>
                rest.elim fun ep₃ rest => rest.elim fun D₃ rest => rest.elim fun B₃ rest => rest.elim fun t₃ rest =>
                rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest => rest.elim fun _ rest =>
                rest.elim fun _ rest => rest.elim fun Y₃ rest => rest.elim fun u₃ rest => rest.elim fun C₃ rest =>
                rest.elim fun β₃ rest => rest.elim fun σ₃ rest => rest.elim fun H₃ rest => rest.elim fun ST₃ rest =>
                rest.elim fun QT₃ rest => rest.elim fun GT₃ rest => rest.elim fun χ₃ rest => rest.elim fun U₃ rest =>
                rest.elim fun V₃ rest => rest.elim fun Γ₃ rest => rest.elim fun k₃ rest => rest.elim fun φ₃ rest =>
                rest.elim fun history₃ rest => rest.elim fun rows₃ rest => rest.elim fun codes₃ rest =>
                rest.elim fun maps₃ rest => rest.elim fun last rest => rest.elim fun bound₃ rest =>
                rest.elim fun _ rest => rest.elim fun _ ready => by
                  obtain ⟨ne,l,r,hl,point,entry,code⟩ := choice
                  have below : M.PairMember I (v 14) (ν.bound 8).val.val (v 1) :=
                    Eq.mpr (congrArg (fun z => M.PairMember I (v 14) z (v 1))
                      (congrArg (fun z => z.val.val) (new_eq 2))) low
                  have parent : Tg_iteration_parent_d hZF v a old.i G₁
                      ⟨v 6,d₁,N₁,R₁,w₂,η₂,C₂,Lr.val,Wr.val,qr,q₁,B₁,σ₁⟩ := by
                    refine ⟨j₁,edge₁,Or.inr ⟨ne,l,r,old,hl,point,entry,code,rfl,
                      p,_,old_code,new_code,(fun i => (ρr.bound ([19,22,40,41,42].get i)).val.val),?_,restart_link⟩⟩
                    intro i
                    exact Eq.mpr (congrArg (fun y => M.PairMember I (p ([19,22,40,41,42].get i)) y j₁)
                      (congrArg Subtype.val (old_eq ([19,22,40,41,42].get i))))
                      (record_points ([19,22,40,41,42].get i))
                  exact h.finish_l hZF mid first tree₃ second lf₃ levels₃ history₃
                    (fun z hz => rows₃ z (rows₁ z hz)) (fun z hz => codes₃ z (codes₁ z hz))
                    (fun z hz => maps₃ z (maps₁ z hz)) last qn₃ edge₃ bound₃ (critical h.critical) ready (funext eq) parent rfl below letters hx

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从非空请求及原档案列直接执行继续轮

规则 (6) 给出较早原轮号，数字图据此选取实际外部行。该行的模型、
完整存档、根基底、共同图和复制历史对应共同供应准备入口的全部旧源数据。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_archive_views_d.continue_l
    {ω T Q G E Λ m H ST QT GT n N S B σ u Y β d c₀ X₀ R₀ w₀ z₀ q C₀
      w' η' C' zn χ γ₀ Bγ o D k S₀ : M.Domain}
    (root : Zc_model_d I ω c₀ X₀ R₀) (numbers : Rr_layer_d I ω X₀ R₀ w₀ z₀)
    (hist : Ic_history_d hZF ω T Q G E Λ m H ST QT GT)
    (tree : It_tree_d hZF ω c₀ m T Q G E)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n)
    (lf : M.IsSetFunction I Λ)
    (levels : ∀ i ρ, Rd_entry_d i ρ Λ ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F)
    (an : Ic_at_d H n N B σ u Y β) (qn : Rd_entry_d n d Q) (mn : Smdl_d I d N S)
    (qr : Rd_entry_d o c₀ Q) (origin : It_map_d G o n q) (image : Rd_entry_d C₀ C' q)
    (current : Tg_context_d I w' N S η' C') (anchor : Tg_anchor_d I γ₀ Bγ N S q)
    (bound : Ic_bound_d I H Q N S σ n χ)
    (nc : Nonempty {x : (smdl_structure_l I (R := S) mn.2.1).Domain //
      (smdl_structure_l I (R := S) mn.2.1).mem x ⟨C',current.member⟩})
    (ι : Env (rt_model_l (M := smdl_structure_l I (R := S) mn.2.1) ⟨C',current.member⟩ nc) 46)
    (issued : Formula.satisfies ι tg_issued0_m) (hw : (ι.bound 0).val.val = w')
    (treeName : Rd_entry_d S₀ (ι.bound 7).val.val q)
    (alphabet : ∃ a, M.mem a Bγ ∧ Rd_entry_d a (ι.bound 6).val.val q)
    (ne : ι.bound 23 ≠ ι.bound 1)
    (index : Tg_round_index_d I ω zn mn.2.1 ⟨w',current.omega_mem⟩ (ι.bound 19).val k)
    (seq : M.IsSequenceOfLength I D k) (links : Tg_archive_links_d I ⟨o,n,Q,G,Λ,H⟩ D)
    (names : Tg_archive_names_d I S₀ D)
    (views : Tg_archive_views_d I ω γ₀ Bγ C₀ D N S B σ w' C' (ι.bound 4).val.val
      (ι.bound 1).val.val (ι.bound 2).val.val (ι.bound 3).val.val zn (ι.bound 20).val.val)
    (below : Rd_entry_d χ (ι.bound 24).val.val S) :
    let right := tree.diagram.elementary o n q c₀ X₀ R₀ d N S origin qr qn root.model mn
    let ground := (root.map_l hZF tree.omega mn right).native_l I hZF tree.omega
    let hN := ZF.modelsKP (ZFC.models_zf_l ground)
    ∃ l r, ∃ s : Tg_archive_row_d M.Domain,
      M.mem l k ∧ Rd_entry_d l (ι.bound 22).val.val zn ∧ Rd_entry_d l r D ∧
      Rt_tuple_d s.values_d r ∧ s.link_d ⟨o,n,Q,G,Λ,H⟩ ∧
      Tg_prepared_d hZF ω T E m QT GT c₀ X₀ R₀ N S B σ d q C₀ S₀ w' η' C' zn χ γ₀ Bγ
        s.i s.c s.X s.R s.w s.η s.C s.L s.U s.q s.p s.A s.π o n Q G Λ H
        mn hN current nc ι tree.omega := by
  intro right ground hN
  let Nn := smdl_structure_l I (R := S) mn.2.1
  let cn : Nn.Domain := ⟨C',current.member⟩
  have fs := current.finite_l mn.2.1 hN.1
  let J := rt_pair_l fs.transitive nc hN.1 fs.pair
  have ext := rt_model_ext_l hN.1 fs.transitive nc
  -- 非空标签的真实规则 (6) 给出较早轮号，不另加选中旧行的假设。
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,fork,_⟩ := tg_issued_query_l J ext ι issued
  have earlier : Nn.mem (ι.bound 22).val (ι.bound 19).val :=
    ((Formula.satisfies_conj_iff ..).mp (fork ne)).1
  obtain ⟨l,r,hl,point,entry⟩ := index.select D seq (ι.bound 22).val.val earlier
  obtain ⟨s,code,mx,saved,⟨zx,nx⟩,basis,l₀,φ₀,V₀,Γ₀,g₀,prior,view⟩ := views l r entry
  obtain ⟨hi,qi,oldRoot,active,z,Z,α,ai⟩ := links l r s entry code
  have left := tree.diagram.elementary o s.i s.p c₀ X₀ R₀ s.c s.X s.R oldRoot qr qi root.model mx
  -- 当前严格候选界同时给出 χ 的反射层所属及继续核所需 δ 界。
  let χn : Nn.Domain := ⟨χ,bound.ordinal.1 0⟩
  have member : Rd_entry_d χ C' S := fs.transitive (ι.bound 24).val (ι.bound 24).property χn below
  let ηn : Nn.Domain := ⟨η',current.height⟩
  have rankC := (rr_rank_native_l I mn.2.1 hN ηn cn).mp ((rr_rank_truth_l I).mpr current.rank)
  have limitC : Nn.IsLimitOrdinal ηn := (Formula.satisfies_isLimitOrdinal_iff ..).mp
    ((rr_truth_native_l I mn.2.1 (Formula.isLimitOrdinal .newest) (by simp -implicitDefEqProofs)
      (fun _ : Fin 1 => ηn)).mp current.limit)
  obtain ⟨boundκ,regular⟩ := tg_issued_control_l hN rankC limitC fs nc ι issued
  have belowδ : Rd_entry_d χ (ι.bound 5).val.val S :=
    regular.isCardinal.1.transitive (ι.bound 24).val boundκ χn below
  have prepared := saved.prepare_l hZFC root numbers hist tree hn hm levels ai an qi qn mx mn
    left right oldRoot origin image current nx index.numbers hi active lf bound member basis (names l r s entry code) anchor
    nc ι issued hw treeName alphabet ne prior view point belowδ
  exact ⟨l,r,s,hl,point,entry,code,links l r s entry code,prepared⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从同一原请求记录实际执行两类后继

先读回所属模型中的请求及外部轮号，再按真实标签分支。两类完整工厂的
实际树、复制历史及末行与给定实数输入共同产生下一有限状态，可直接继续调用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 下一请求的真实记录直接驱动后继，不再要求调用方先提供反射层中的请求环境。 -/
private theorem tg_request_prepare_l
    {ω c₀ X₀ R₀ w₀ z₀ n m T Q G E Λ H ST QT GT N R B σ u U β d o q
      C₀ S₀ γ Bγ w η C z χ k D r : M.Domain} {v : Fin 46 → M.Domain}
    (root : Zc_model_d I ω c₀ X₀ R₀) (numbers : Rr_layer_d I ω X₀ R₀ w₀ z₀)
    (tree : It_tree_d hZF ω c₀ m T Q G E)
    (hist : Ic_history_d hZF ω T Q G E Λ m H ST QT GT)
    (hn : M.mem n ω) (hm : M.SuccessorOf m n) (lf : M.IsSetFunction I Λ)
    (levels : ∀ i ρ, Rd_entry_d i ρ Λ ↔ ∃ p κ F, Rd_entry_d i p E ∧ It_payload_d p κ ρ F)
    (an : Ic_at_d H n N B σ u U β) (qn : Rd_entry_d n d Q) (mn : Smdl_d I d N R)
    (qr : Rd_entry_d o c₀ Q) (origin : It_map_d G o n q)
    (basis : Tg_basis_d I γ Bγ C₀ w N R C q) (bound : Ic_bound_d I H Q N R σ n χ)
    (alphabet : ∃ a, M.mem a Bγ ∧ Rd_entry_d a (v 6) q)
    (state : Tg_request_state_d I ω γ Bγ C₀ S₀ N R w η C B σ χ z k D r ⟨o,n,Q,G,Λ,H⟩ v) :
    let right := tree.diagram.elementary o n q c₀ X₀ R₀ d N R origin qr qn root.model mn
    let ground := (root.map_l hZF tree.omega mn right).native_l I hZF tree.omega
    let hN := ZF.modelsKP (ZFC.models_zf_l ground)
    ∃ nc : Nonempty {x : (smdl_structure_l I (R := R) mn.2.1).Domain //
      (smdl_structure_l I (R := R) mn.2.1).mem x ⟨C,state.context.member⟩},
    ∃ ι : Env (rt_model_l (M := smdl_structure_l I (R := R) mn.2.1)
      ⟨C,state.context.member⟩ nc) 46,
      (∀ i, (ι.bound i).val.val = v i) ∧ Formula.satisfies ι tg_issued0_m ∧
      Tg_round_index_d I ω z mn.2.1 ⟨w,state.context.omega_mem⟩ (ι.bound 19).val k ∧
      ((v 23 = v 1 ∧
        Tg_reset_native_d hZF ω c₀ X₀ R₀ n m T Q G E Λ H QT GT N R B σ u U β d o q
          C₀ S₀ γ Bγ w η C z χ mn hN state.context nc ι) ∨
       (v 23 ≠ v 1 ∧ ∃ l s, ∃ a : Tg_archive_row_d M.Domain,
        M.mem l k ∧ Rd_entry_d l (v 22) z ∧ Rd_entry_d l s D ∧
        Rt_tuple_d a.values_d s ∧ a.link_d ⟨o,n,Q,G,Λ,H⟩ ∧
        Tg_prepared_d hZF ω T E m QT GT c₀ X₀ R₀ N R B σ d q C₀ S₀ w η C z χ γ Bγ
          a.i a.c a.X a.R a.w a.η a.C a.L a.U a.q a.p a.A a.π o n Q G Λ H
          mn hN state.context nc ι tree.omega)) := by
  intro right ground hN
  obtain ⟨nc,ι,eq,issued,index⟩ := state.read_l I (ZF.modelsKP hZF) hN.1
  have hw : (ι.bound 0).val.val = w := (eq 0).trans state.omega
  have lower : It_lower_d I γ N R (ι.bound 24).val.val := (eq 24).symm ▸ state.lower
  have below : Rd_entry_d χ (ι.bound 24).val.val R := (eq 24).symm ▸ state.below
  obtain ⟨p,hp,name⟩ := state.name
  have rootEq := tree.diagram.map_unique_l hZF hp origin
  have name : Rd_entry_d S₀ (v 7) q := rootEq ▸ name
  have treeName : Rd_entry_d S₀ (ι.bound 7).val.val q :=
    Eq.mpr (congrArg (fun S => Rd_entry_d S₀ S q) (eq 7)) name
  refine ⟨nc,ι,eq,issued,index,?_⟩
  rcases Classical.em (v 23 = v 1) with empty | ne
  · have same : ι.bound 23 = ι.bound 1 := Subtype.ext (Subtype.ext
      ((eq 23).trans (empty.trans (eq 1).symm)))
    exact Or.inl ⟨empty,state.context.reset_native_l hZFC root tree hist hn hm lf levels an qn mn qr
      origin basis state.numbers bound nc ι issued hw treeName lower same below⟩
  · have distinct : ι.bound 23 ≠ ι.bound 1 := fun h => ne
      ((eq 23).symm.trans ((congrArg (fun x => x.val.val) h).trans (eq 1)))
    have letters : ∃ a, M.mem a Bγ ∧ Rd_entry_d a (ι.bound 6).val.val q :=
      (eq 6).symm ▸ alphabet
    have views : Tg_archive_views_d I ω γ Bγ C₀ D N R B σ w C (ι.bound 4).val.val
        (ι.bound 1).val.val (ι.bound 2).val.val (ι.bound 3).val.val z (ι.bound 20).val.val := by
      simpa only [eq] using state.views
    obtain ⟨l,s,a,hl,point,entry,code,link,prepared⟩ := views.continue_l hZFC root numbers hist tree
      hn hm lf levels an qn mn qr origin basis.1 state.context (basis.anchor_l I) bound nc ι
      issued hw treeName letters distinct index state.sequence state.links state.names below
    exact Or.inr ⟨ne,l,s,a,hl,(eq 22) ▸ point,entry,code,link,prepared⟩

/-- 给定原输入后，两类实际工厂共同闭合下一次可直接调用的有限状态。 -/
theorem Tg_iteration_d.advance_l
    {ω c₀ X₀ R₀ w₀ z₀ o C₀ S₀ γ Bγ A x : M.Domain}
    {v : Fin 29 → M.Domain} {a : Fin 46 → M.Domain}
    (root : Zc_model_d I ω c₀ X₀ R₀) (numbers : Rr_layer_d I ω X₀ R₀ w₀ z₀)
    (h : Tg_iteration_d hZF ω c₀ o C₀ S₀ γ Bγ A v a)
    (letters : M.mem A Bγ) (hx : M.mem x A) :
    ∃ w b, Tg_iteration_d hZF ω c₀ o C₀ S₀ γ Bγ A w b ∧ Tg_iteration_next_d hZF ω c₀ x v w a b := by
  obtain ⟨nc,ι,eq,_,_,branches⟩ := tg_request_prepare_l hZFC root numbers h.tree h.history
    h.finite h.successor h.levels_function h.levels h.row h.node h.model h.root_node h.root_map
    h.basis h.bound ⟨A,letters,h.alphabet⟩ h.request
  rcases branches with ⟨_,reset⟩ | ⟨ne,l,s,old,hl,point,entry,code,_,prepared⟩
  · exact reset.iteration_l hZF h _ nc ι eq letters hx
  · exact prepared.iteration_l hZF h _ nc ι eq
      ⟨ne,l,s,hl,point,entry,code⟩ letters hx

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 完整状态码直接调用实际后继

输入码解出原状态，原工厂执行给定字母，再编码同一次结果。关系中保留全部树、
复制历史、原局以及奇数存档方程，供一次性的内部选择使用。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)

def Tg_iteration_edge_d (ω c x s t : M.Domain) : Prop := ∃ v w : Fin 75 → M.Domain,
  Rt_tuple_d v s ∧ Rt_tuple_d w t ∧ Tg_iteration_next_d hZF ω c x
    (fun i => v (i.castAdd 46)) (fun i => w (i.castAdd 46))
    (fun i => v (Fin.natAdd 29 i)) (fun i => w (Fin.natAdd 29 i))

def tg_iteration_edge_m {d} (ω c x s t : Term d) : Formula 1 d :=
  let e : Term d → Term (75+d) := fun z => z.rename (Fin.natAdd 75)
  let f : Term (75+d) → Term (75+(75+d)) := fun z => z.rename (Fin.natAdd 75)
  let v : Fin 75 → Term (75+(75+d)) := fun i => f (.bound (i.castAdd d))
  let w : Fin 75 → Term (75+(75+d)) := fun i => .bound (i.castAdd (75+d))
  rb_exists_m (n := 75) (rb_exists_m (n := 75) (.conj (rt_tuple_m v (f (e s)))
    (.conj (rt_tuple_m w (f (e t))) (tg_iteration_next_m (f (e ω)) (f (e c)) (f (e x))
      (fun i => v (i.castAdd 46)) (fun i => w (i.castAdd 46))
      (fun i => v (Fin.natAdd 29 i)) (fun i => w (Fin.natAdd 29 i))))))

@[simp] theorem tg_iteration_edge_closed_l {d} (ω c x s t : Term d)
    (hω : ω.freeSupport = []) (hc : c.freeSupport = []) (hx : x.freeSupport = [])
    (hs : s.freeSupport = []) (ht : t.freeSupport = []) : (tg_iteration_edge_m ω c x s t).FreeClosed := by
  simp -implicitDefEqProofs [tg_iteration_edge_m,Definitional.Formula.FreeClosed,hω,hc,hx]
  exact ⟨rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using hs),
    rt_tuple_closed_l _ _ (fun _ => rfl) (by simpa using ht)⟩

theorem tg_iteration_edge_sat_l {d} (ρ : Env M d) (ω c x s t : Term d) :
    Formula.satisfies ρ (tg_iteration_edge_m ω c x s t) ↔
      Tg_iteration_edge_d hZF (ω.eval ρ) (c.eval ρ) (x.eval ρ) (s.eval ρ) (t.eval ρ) := by
  simp only [tg_iteration_edge_m,Tg_iteration_edge_d,rb_exists_sat_l,Formula.satisfies_conj_iff,
    rt_tuple_sat_l hZF.1,tg_iteration_next_sat_l hZF,Definitional.Term.eval_rename,
    Env.reindex,Function.comp_def,Term.eval_bound,Fin.addCases_left,Fin.addCases_right]

theorem Tg_iteration_edge_d.read_l {ω c x s t : M.Domain} {v w : Fin 75 → M.Domain}
    (h : Tg_iteration_edge_d hZF ω c x s t) (ps : Rt_tuple_d v s) (pt : Rt_tuple_d w t) :
    Tg_iteration_next_d hZF ω c x (fun i => v (i.castAdd 46)) (fun i => w (i.castAdd 46))
      (fun i => v (Fin.natAdd 29 i)) (fun i => w (Fin.natAdd 29 i)) := by
  obtain ⟨a,b,pa,pb,next⟩ := h
  exact (rt_tuple_inj_l pa ps) ▸ (rt_tuple_inj_l pb pt) ▸ next

variable (hZFC : M.Models ZFC)
local notation "J" => kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))

theorem Tg_iteration_code_d.advance_l
    {ω c X₀ R₀ w₀ z₀ o C₀ S₀ γ Bγ A x s : M.Domain}
    (root : Zc_model_d J ω c X₀ R₀) (numbers : Rr_layer_d J ω X₀ R₀ w₀ z₀)
    (h : Tg_iteration_code_d (ZFC.models_zf_l hZFC) ω c o C₀ S₀ γ Bγ A s)
    (letters : M.mem A Bγ) (hx : M.mem x A) : ∃ t,
      Tg_iteration_code_d (ZFC.models_zf_l hZFC) ω c o C₀ S₀ γ Bγ A t ∧
      Tg_iteration_edge_d (ZFC.models_zf_l hZFC) ω c x s t := by
  obtain ⟨v,code,state⟩ := h
  obtain ⟨w,b,next,edge⟩ := state.advance_l hZFC root numbers letters hx
  let q : Fin 75 → M.Domain := Fin.addCases (motive := fun _ => M.Domain) w b
  obtain ⟨t,tuple⟩ := rt_tuple_exists_l (ZF.modelsKP (ZFC.models_zf_l hZFC)) q
  refine ⟨t,⟨q,tuple,?_⟩,v,q,code,tuple,?_⟩
  · simpa only [q,Fin.addCases_left,Fin.addCases_right] using next
  · simpa only [q,Fin.addCases_left,Fin.addCases_right] using edge

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 所有原输入共用的一次性后继选择

完整状态及完整后继均已在对象语言中编码。反射闭包和集合选择构造同一张响应表，
以后递归只查询这张表，不按未来对局重新选择原树或工作复制。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

structure Tg_iteration_choice_d (hZF : M.Models ZF) (ω c o C₀ S₀ γ Bγ A r X D K : M.Domain) : Prop where
  initial : Tg_iteration_code_d hZF ω c o C₀ S₀ γ Bγ A r
  member : M.mem r X
  product : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) D X A
  function : Fn0_d D X K
  step : ∀ s x t p, Tg_iteration_code_d hZF ω c o C₀ S₀ γ Bγ A s →
    (kp_pair_l (ZF.modelsKP hZF)).Codes p s x → Rd_entry_d p t K →
    Tg_iteration_code_d hZF ω c o C₀ S₀ γ Bγ A t ∧ Tg_iteration_edge_d hZF ω c x s t

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_iteration_code_d.choice_l {ω c X₀ R₀ w₀ z₀ o C₀ S₀ γ Bγ A r : M.Domain}
    (root : Zc_model_d I ω c X₀ R₀) (numbers : Rr_layer_d I ω X₀ R₀ w₀ z₀)
    (initial : Tg_iteration_code_d hZF ω c o C₀ S₀ γ Bγ A r) (letters : M.mem A Bγ) :
    ∃ X D K, Tg_iteration_choice_d hZF ω c o C₀ S₀ γ Bγ A r X D K := by
  have hw : M.IsOmega ω := initial.elim fun _ h => h.2.tree.omega
  let ρ : Env M 8 := ⟨fun i => [ω,c,o,C₀,S₀,γ,Bγ,A].get i,fun _ => ω⟩
  let V : UnarySchema 8 := { body := (tg_iteration_code_m (.bound 1) (.bound 2) (.bound 3)
    (.bound 4) (.bound 5) (.bound 6) (.bound 7) (.bound 8) .newest) }
  let φ : UnarySchema 10 := { body := tg_iteration_edge_m (.bound 3) (.bound 4) (.bound 1) (.bound 2) .newest }
  have valid s : V.denote ρ s ↔ Tg_iteration_code_d hZF ω c o C₀ S₀ γ Bγ A s :=
    tg_iteration_code_sat_l hZF ..
  have action s x t : φ.denote ((ρ.push s).push x) t ↔ Tg_iteration_edge_d hZF ω c x s t :=
    tg_iteration_edge_sat_l hZF ..
  obtain ⟨X,D,K,member,product,function,steps⟩ := ZFC.class_response_l I hZFC V φ ρ (a := r) hw (by
    intro s x hs hx
    obtain ⟨t,next,edge⟩ := ((valid s).mp hs).advance_l hZFC root numbers letters hx
    exact ⟨t,(valid t).mpr next,(action s x t).mpr edge⟩)
  refine ⟨X,D,K,⟨initial,member,product,fn0_of_function_l (ZF.modelsKP hZF) function,?_⟩⟩
  intro s x t p state pair entry
  obtain ⟨next,edge⟩ := steps s x t p pair entry ((valid s).mpr state)
  exact ⟨(valid t).mp next,(action s x t).mp edge⟩

/-- 已实现的共同有限状态直接产生全输入响应表。 -/
theorem Tg_iteration_d.choice_l {ω c X₀ R₀ w₀ z₀ o C₀ S₀ γ Bγ A : M.Domain}
    {v : Fin 29 → M.Domain} {a : Fin 46 → M.Domain}
    (root : Zc_model_d I ω c X₀ R₀) (numbers : Rr_layer_d I ω X₀ R₀ w₀ z₀)
    (h : Tg_iteration_d hZF ω c o C₀ S₀ γ Bγ A v a) (letters : M.mem A Bγ) :
    ∃ r X D K, Rt_tuple_d (Fin.addCases (m := 29) (n := 46) (motive := fun _ => M.Domain) v a) r ∧
      Tg_iteration_choice_d hZF ω c o C₀ S₀ γ Bγ A r X D K := by
  obtain ⟨r,code,initial⟩ := h.pack_l hZF
  obtain ⟨X,D,K,choice⟩ := initial.choice_l hZFC root numbers letters
  exact ⟨r,X,D,K,code,choice⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一响应表上的完整内部ω运行

对象模型自身的ω归纳保持完整状态和精确外部轮号。每个相邻阶段保留实际输入、
两次树延伸、复制历史以及奇数边方程；选择表在所有对局之前统一固定。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

structure Tg_iteration_run_d (ω c o C₀ S₀ γ Bγ A X K r a f H : M.Domain) : Prop where
  recursion : Gi_d hZF true ω X K r a f H
  rows : ∀ n s, Rd_entry_d n s H →
    Tg_iteration_code_d hZF ω c o C₀ S₀ γ Bγ A s ∧ Rt_coord_d (27 : Fin 75) s n
  steps : ∀ i j s t, M.SuccessorOf j i → Rd_entry_d i s H → Rd_entry_d j t H →
    ∃ x, Gi_input_d hZF true ω a f i x ∧ Tg_iteration_edge_d hZF ω c x s t

/-- 原后继中的实际轮号后继与元组唯一性保持内部索引。 -/
private theorem tg_iteration_edge_index_l {ω c x s t i j : M.Domain}
    (edge : Tg_iteration_edge_d hZF ω c x s t) (old : Rt_coord_d (27 : Fin 75) s i)
    (succ : M.SuccessorOf j i) : Rt_coord_d (27 : Fin 75) t j := by
  obtain ⟨v,w,ps,pt,next⟩ := edge
  have index : v 27 = i := old.read_l v ps
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,step,_⟩ := next
  have step : M.SuccessorOf (w 27) i := index ▸ step
  exact ⟨w,pt,step.eq hZF.1 succ⟩

theorem Tg_iteration_choice_d.validate_l {ω c o C₀ S₀ γ Bγ A r X D K a f H : M.Domain}
    (h : Tg_iteration_choice_d hZF ω c o C₀ S₀ γ Bγ A r X D K)
    (zero : Rt_coord_d (27 : Fin 75) r o) (empty : ∀ z, ¬ M.mem z o)
    (run : Gi_d hZF true ω X K r a f H) :
    Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H := by
  have hw : M.IsOmega ω := h.initial.elim fun _ h => h.2.tree.omega
  let ρ : Env M 9 := ⟨fun i => [ω,c,o,C₀,S₀,γ,Bγ,A,H].get i,fun _ => ω⟩
  let φ : UnarySchema 9 := { body := set[10] ⟪∀ s,
    ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 10)⌝ₛ,s,⌜(.bound 9 : Term 10)⌝ₛ) →
    ⌜tg_iteration_code_m⌝ₚ(⌜(.bound 1 : Term 10)⌝ₛ,⌜(.bound 2 : Term 10)⌝ₛ,⌜(.bound 3 : Term 10)⌝ₛ,
      ⌜(.bound 4 : Term 10)⌝ₛ,⌜(.bound 5 : Term 10)⌝ₛ,⌜(.bound 6 : Term 10)⌝ₛ,
      ⌜(.bound 7 : Term 10)⌝ₛ,⌜(.bound 8 : Term 10)⌝ₛ,s) ∧
    ⌜(rt_coord_m (27 : Fin 75))⌝ₚ(s,⌜(.newest : Term 10)⌝ₛ)⟫ }
  have sat n : φ.denote ρ n ↔ ∀ s, Rd_entry_d n s H →
      Tg_iteration_code_d hZF ω c o C₀ S₀ γ Bγ A s ∧ Rt_coord_d (27 : Fin 75) s n := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      rd_entry0_sat_l hZF.1,Formula.satisfies_conj_iff,tg_iteration_code_sat_l hZF,
      rt_coord_sat_l hZF.1,Definitional.Term.eval_weaken]; rfl
  have all : ∀ n, M.mem n ω → ∀ s, Rd_entry_d n s H →
      Tg_iteration_code_d hZF ω c o C₀ S₀ γ Bγ A s ∧ Rt_coord_d (27 : Fin 75) s n := by
    apply hw.induction
    · obtain ⟨B,bs⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨B,fun n => (bs n).trans (and_congr_right fun _ => sat n)⟩
    · intro z hz s hs
      have zo := hZF.1.eq_of_same_members z o (fun x => iff_of_false (hz x) (empty x))
      have sr := (fn0_function_l (ZF.modelsKP hZF) run.1).1.2 z s r hs (run.2.1 z hz)
      exact ⟨sr.symm ▸ h.initial,sr.symm ▸ zo.symm ▸ zero⟩
    · intro i hi ih j succ t ht
      obtain ⟨s,_,hs⟩ := run.1.2.1 i hi
      obtain ⟨x,p,_,pair,entry⟩ := run.2.2 i j s t succ hs ht
      obtain ⟨next,edge⟩ := h.step s x t p (ih s hs).1 pair entry
      exact ⟨next,tg_iteration_edge_index_l hZF edge (ih s hs).2 succ⟩
  have rows n s (hs : Rd_entry_d n s H) := all n (run.1.bound_l hs).1 s hs
  refine ⟨run,rows,?_⟩
  intro i j s t succ hs ht
  obtain ⟨x,p,input,pair,entry⟩ := run.2.2 i j s t succ hs ht
  exact ⟨x,input,(h.step s x t p (rows i s hs).1 pair entry).2⟩

theorem Tg_iteration_choice_d.run_l {ω c o C₀ S₀ γ Bγ A r X D K a f : M.Domain}
    (h : Tg_iteration_choice_d hZF ω c o C₀ S₀ γ Bγ A r X D K)
    (zero : Rt_coord_d (27 : Fin 75) r o) (empty : ∀ z, ¬ M.mem z o)
    (ha : M.mem a A) (ff : M.IsSetFunction I f) (range : ∀ i x, Rd_entry_d i x f → M.mem x A) :
    ∃ H, Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H := by
  have hw : M.IsOmega ω := h.initial.elim fun _ h => h.2.tree.omega
  obtain ⟨H,run⟩ := gi_exists_l hZF (b := true) hw h.product h.function h.member ha ff range
  exact ⟨H,h.validate_l hZF zero empty run⟩

variable (hZFC : M.Models ZFC)
local notation "hZ" => ZFC.models_zf_l hZFC
local notation "J" => kp_pair_l (ZF.modelsKP hZ)

/-- 实际零轮先固定一张响应表，再对每份原输入构造内部全ω运行。 -/
theorem Tg_iteration_d.recursion_l {ω c X₀ R₀ w₀ z₀ o C₀ S₀ γ Bγ A a : M.Domain}
    {v : Fin 29 → M.Domain} {u : Fin 46 → M.Domain}
    (root : Zc_model_d J ω c X₀ R₀) (numbers : Rr_layer_d J ω X₀ R₀ w₀ z₀)
    (initial : Tg_iteration_d hZ ω c o C₀ S₀ γ Bγ A v u) (zero : v 27 = o)
    (empty : ∀ z, ¬ M.mem z o) (letters : M.mem A Bγ) (ha : M.mem a A) :
    ∃ r X D K, Tg_iteration_choice_d hZ ω c o C₀ S₀ γ Bγ A r X D K ∧
      Rt_tuple_d (Fin.addCases (m := 29) (n := 46) (motive := fun _ => M.Domain) v u) r ∧
      ∀ f, Fn0_d ω A f → ∃ H, Tg_iteration_run_d hZ ω c o C₀ S₀ γ Bγ A X K r a f H := by
  obtain ⟨r,X,D,K,code,choice⟩ := initial.choice_l hZFC root numbers letters
  have index : Rt_coord_d (27 : Fin 75) r o := ⟨_,code,
    (Fin.addCases_left (m := 29) (n := 46) (motive := fun _ => M.Domain) (left := v) (right := u) 27).trans zero⟩
  refine ⟨r,X,D,K,choice,code,fun f ff => ?_⟩
  exact choice.run_l hZ index empty ha (fn0_function_l (ZF.modelsKP hZ) ff).1
    (fun _ _ h => (ff.bound_l h).2)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一状态码中的背景原局及实际末项

原局直接取第28项，其定义域是第27项外部轮号。读取无需把原关系模型换成隶属模型。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Tg_iteration_code_d.play_l {ω c o C₀ S₀ γ Bγ A r f : M.Domain}
    (h : Tg_iteration_code_d hZF ω c o C₀ S₀ γ Bγ A r) (play : Rt_coord_d (28 : Fin 75) r f) :
    ∃ n, Rt_coord_d (27 : Fin 75) r n ∧ Fn0_d n A f := by
  obtain ⟨v,code,state⟩ := h
  exact ⟨v 27,⟨v,code,rfl⟩,(play.read_l v code) ▸ state.play.1⟩

/-- 完整后继中的前缀追加给出实际末项，并沿原轮号读取偶数落子规则。 -/
theorem Tg_iteration_edge_d.last_l {ω c o C₀ S₀ γ Bγ A x s t n : M.Domain}
    (edge : Tg_iteration_edge_d hZF ω c x s t)
    (old : Tg_iteration_code_d hZF ω c o C₀ S₀ γ Bγ A s) (index : Rt_coord_d (27 : Fin 75) s n) :
    ∃ m f g y, Rt_coord_d (27 : Fin 75) t m ∧ Rt_coord_d (28 : Fin 75) s f ∧
      Rt_coord_d (28 : Fin 75) t g ∧ M.SuccessorOf m n ∧ Fseq_end_d I ω g f y ∧
      Rd_entry_d n y g ∧ (Gm_even_d I ω n → y = x) := by
  obtain ⟨v,w,ps,pt,next⟩ := edge
  have current : Rt_coord_d (28 : Fin 75) s (v 28) := ⟨v,ps,rfl⟩
  obtain ⟨n',num,fn⟩ := old.play_l hZF current
  have fn : Fn0_d n A (v 28) := num.unique_l index ▸ fn
  have vn : v 27 = n := index.read_l v ps
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,succ,y,ends,even,_⟩ := next
  obtain ⟨l,k,last⟩ := ends
  have kn := last.prefix_sequence.2.2.2.eq hZF.1 (fn0_function_l (ZF.modelsKP hZF) fn).2.1
  exact ⟨w 27,v 28,w 28,y,⟨w,pt,rfl⟩,current,⟨w,pt,rfl⟩,vn ▸ succ,
    ⟨l,k,last⟩,kn ▸ last.last_value,vn ▸ even⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一响应表上的实际原博弈策略

有限输入先递归到其长度，再用固定字母查询下一状态，并读取该状态原局的末项。
递归因果性和状态码唯一性保证输出唯一；替换实际收集整张策略函数。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Tg_iteration_response_d (ω X K r a s y : M.Domain) : Prop := ∃ n H u p t q,
  M.IsDomainOf I n s ∧ Gi_d hZF true ω X K r a s H ∧ Rd_entry_d n u H ∧
    (I).Codes p u a ∧ Rd_entry_d p t K ∧ Rt_coord_d (28 : Fin 75) t q ∧ Rd_entry_d n y q

def tg_iteration_response_m {d} (ω X K r a s y : Term d) : Formula 1 d := set[d] ⟪∃ n H u p t q,
  ⌜Formula.isDomain kpair_convention_l⌝ₚ(n,⌜s⌝ₛ) ∧
  ⌜(gi_m true)⌝ₚ(⌜ω⌝ₛ,⌜X⌝ₛ,⌜K⌝ₛ,⌜r⌝ₛ,⌜a⌝ₛ,⌜s⌝ₛ,H) ∧
  ⌜rd_entry0_m⌝ₚ(n,u,H) ∧ ⌜kpair_m⌝ₚ(p,u,⌜a⌝ₛ) ∧ ⌜rd_entry0_m⌝ₚ(p,t,⌜K⌝ₛ) ∧
  ⌜(rt_coord_m (28 : Fin 75))⌝ₚ(t,q) ∧ ⌜rd_entry0_m⌝ₚ(n,⌜y⌝ₛ,q)⟫
derive_free_closed tg_iteration_response_m

theorem tg_iteration_response_sat_l {d} (ρ : Env M d) (ω X K r a s y : Term d) :
    Formula.satisfies ρ (tg_iteration_response_m ω X K r a s y) ↔
      Tg_iteration_response_d hZF (ω.eval ρ) (X.eval ρ) (K.eval ρ) (r.eval ρ) (a.eval ρ) (s.eval ρ) (y.eval ρ) := by
  simp only [tg_iteration_response_m,Tg_iteration_response_d,Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,Formula.satisfies_isDomain_iff I,gi_sat_l hZF true,
    rd_entry0_sat_l hZF.1,kpair_sat_l M hZF.1,rt_coord_sat_l hZF.1,Definitional.Term.eval_weaken]; rfl

theorem Tg_iteration_choice_d.response_l {ω c o C₀ S₀ γ Bγ A r X D K a s n : M.Domain}
    (h : Tg_iteration_choice_d hZF ω c o C₀ S₀ γ Bγ A r X D K)
    (zero : Rt_coord_d (27 : Fin 75) r o) (empty : ∀ z, ¬ M.mem z o)
    (ha : M.mem a A) (hn : M.mem n ω) (fs : M.IsSetFunctionFromTo I s n A) :
    ∃ y, Tg_iteration_response_d hZF ω X K r a s y := by
  obtain ⟨H,run⟩ := h.run_l hZF zero empty ha fs.1 (fun _ _ hi => fs.output_mem_of_pairMember hi)
  obtain ⟨u,hu,nu⟩ := run.recursion.1.2.1 n hn
  obtain ⟨p,pair⟩ := (I).total u a
  obtain ⟨t,_,pt⟩ := h.function.2.1 p ((h.product p).mpr ⟨u,hu,a,ha,pair⟩)
  have state := run.rows n u nu
  obtain ⟨_,edge⟩ := h.step u a t p state.1 pair pt
  obtain ⟨_,_,q,y,_,_,coord,_,_,last,_⟩ := edge.last_l hZF state.1 state.2
  exact ⟨y,n,H,u,p,t,q,fs.2.1,run.recursion,nu,pair,pt,coord,last⟩

theorem Tg_iteration_choice_d.response_bound_l {ω c o C₀ S₀ γ Bγ A r X D K a s y : M.Domain}
    (h : Tg_iteration_choice_d hZF ω c o C₀ S₀ γ Bγ A r X D K)
    (zero : Rt_coord_d (27 : Fin 75) r o) (empty : ∀ z, ¬ M.mem z o)
    (answer : Tg_iteration_response_d hZF ω X K r a s y) : M.mem y A := by
  obtain ⟨n,H,u,p,t,q,_,run,nu,pair,pt,coord,last⟩ := answer
  have state := (h.validate_l hZF zero empty run).rows n u nu
  have next := (h.step u a t p state.1 pair pt).1
  obtain ⟨_,_,fn⟩ := next.play_l hZF coord
  exact (fn.bound_l last).2

theorem Tg_iteration_choice_d.response_unique_l {ω c o C₀ S₀ γ Bγ A r X D K a s x y : M.Domain}
    (h : Tg_iteration_choice_d hZF ω c o C₀ S₀ γ Bγ A r X D K)
    (zero : Rt_coord_d (27 : Fin 75) r o) (empty : ∀ z, ¬ M.mem z o)
    (fs : M.IsSetFunction I s) (hx : Tg_iteration_response_d hZF ω X K r a s x)
    (hy : Tg_iteration_response_d hZF ω X K r a s y) : x = y := by
  have hw : M.IsOmega ω := h.initial.elim fun _ h => h.2.tree.omega
  obtain ⟨n,H,u,p,t,q,dom,run,nu,pair,pt,coord,last⟩ := hx
  obtain ⟨n',H',u',p',t',q',dom',run',nu',pair',pt',coord',last'⟩ := hy
  have nn := dom'.eq hZF.1 dom
  subst n'
  have fk := (fn0_function_l (ZF.modelsKP hZF) h.function).1
  have uu := run.agree_l hZF hw fk fs run' (run.1.bound_l nu).1 (fun _ _ _ => Iff.rfl) u u' nu nu'
  have pp := (I).unique pair (uu.symm ▸ pair')
  have tt := fk.2 p t t' pt (pp.symm ▸ pt')
  have qq := coord.unique_l (tt.symm ▸ coord')
  have state := (h.validate_l hZF zero empty run).rows n u nu
  have next := (h.step u a t p state.1 pair pt).1
  obtain ⟨_,_,fn⟩ := next.play_l hZF coord
  exact (fn0_function_l (ZF.modelsKP hZF) fn).1.2 n x y last (qq.symm ▸ last')

theorem Tg_iteration_choice_d.strategy_l {ω c o C₀ S₀ γ Bγ A r X D K a F : M.Domain}
    (h : Tg_iteration_choice_d hZF ω c o C₀ S₀ γ Bγ A r X D K)
    (zero : Rt_coord_d (27 : Fin 75) r o) (empty : ∀ z, ¬ M.mem z o)
    (ha : M.mem a A) (space : Fseq_space_d I ω A F) : ∃ σ, Fn0_d F A σ ∧
      ∀ s y, Rd_entry_d s y σ ↔ M.mem s F ∧ Tg_iteration_response_d hZF ω X K r a s y := by
  let ρ : Env M 5 := ⟨fun i => [ω,X,K,r,a].get i,fun _ => ω⟩
  let φ : BinarySchema 5 := { body := (tg_iteration_response_m (.bound 2) (.bound 3) (.bound 4)
    (.bound 5) (.bound 6) (.bound 1) .newest) }
  have sat s y : φ.denote ρ s y ↔ Tg_iteration_response_d hZF ω X K r a s y :=
    tg_iteration_response_sat_l hZF ..
  obtain ⟨σ,fn,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := F) (target := A) (by
    intro s hs
    obtain ⟨n,hn,fs⟩ := (space s).mp hs
    obtain ⟨y,hy⟩ := h.response_l hZF zero empty ha hn fs
    exact ⟨y,(sat s y).mpr hy⟩) (by
    intro s hs x y hx hy
    obtain ⟨_,_,fs⟩ := (space s).mp hs
    exact h.response_unique_l hZF zero empty fs.1 ((sat s x).mp hx) ((sat s y).mp hy)) (by
    intro s y _ hy
    exact h.response_bound_l hZF zero empty ((sat s y).mp hy))
  exact ⟨σ,fn0_of_function_l (ZF.modelsKP hZF) fn,fun s y => (values s y).trans (and_congr_right fun _ => sat s y)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 真实原关系运行的内部并树

实际两步延伸保持六张原列及旧终点的全部前驱。内部归纳证明树长覆盖外部轮号，
故同一运行给出共尾有限框架；公共并树定理随后构造长度为ω的原树。
原树不要求nice性质，该性质仍须由后续完整工作复制历史提供。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 原树六列的实际并及每个有限阶段上的精确限制。 -/
structure Tg_iteration_union_d (ω c γ H : M.Domain) (U : Fin 6 → M.Domain) : Prop where
  tree : It_tree_d hZF ω c ω (U 0) (U 1) (U 2) (U 3)
  critical : It_critical_bound_d I γ (U 1) (U 3)
  levels_function : M.IsSetFunction I (U 4)
  levels : ∀ i L, Rd_entry_d i L (U 4) ↔ ∃ p κ F, Rd_entry_d i p (U 3) ∧ It_payload_d p κ L F
  archive : M.IsSequenceOfLength I (U 5) ω
  columns : ∀ b x, M.mem x (U b) ↔ Tg_run_value_d (n := 74) ⟨8+b.val,by omega⟩ H x
  restriction : ∀ i s (v : Fin 75 → M.Domain), Rd_entry_d i s H → Rt_tuple_d v s →
    ∀ x y, M.mem y (v 6) → (Rd_entry_d x y (U 0) ↔ Rd_entry_d x y (v 8))

/-- 保持关系来自同一次实际延伸和档案追加。 -/
theorem Tg_iteration_next_d.keep_l {ω c o C₀ S₀ γ Bγ A x : M.Domain} {v w : Fin 75 → M.Domain}
    (h : Tg_iteration_d hZF ω c o C₀ S₀ γ Bγ A (fun i => v (i.castAdd 46)) (fun i => v (Fin.natAdd 29 i)))
    (g : Tg_iteration_d hZF ω c o C₀ S₀ γ Bγ A (fun i => w (i.castAdd 46)) (fun i => w (Fin.natAdd 29 i)))
    (step : Tg_iteration_next_d hZF ω c x (fun i => v (i.castAdd 46)) (fun i => w (i.castAdd 46))
      (fun i => v (Fin.natAdd 29 i)) (fun i => w (Fin.natAdd 29 i))) :
    Tg_tree_keep_d (fun i => v (i.castAdd 61)) (fun i => w (i.castAdd 61)) := by
  obtain ⟨k,T,Q,G,E,j,mid,e,e',even,_,_,_,_,_,_,y,_,_,row,r,_,_,_,past⟩ := step
  obtain ⟨order,t,q,gmap,move⟩ := h.tree.extension_keep_l hZF e
  obtain ⟨order',t',q',gmap',move'⟩ := mid.extension_keep_l hZF e'
  have sub {a b : M.Domain} (s : M.SuccessorOf b a) : M.MemberSubset a b := fun x hx => (s x).mpr (Or.inl hx)
  have moves : M.MemberSubset (v 11) (w 11) := fun x hx => move' x (move x hx)
  have levels := it_levels_subset_l hZF.1 h.levels_function.1
    (fun i l => (h.levels i l).mp) (fun i l => (g.levels i l).mpr) moves
  have archive : M.MemberSubset (v 13) (w 13) := by
    intro p hp
    obtain ⟨i,s,pair⟩ := h.request.sequence.2.1.1 p hp
    obtain ⟨p',pair',hp'⟩ := (past i s).mpr (Or.inl ⟨p,pair,hp⟩)
    exact kpair_unique_l M hZF.1 pair' pair ▸ hp'
  have keep (a : Fin 6) : M.MemberSubset (v ⟨8+a.val,by omega⟩) (w ⟨8+a.val,by omega⟩) := by
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)))))) a
    · exact fun x hx => t' x (t x hx)
    · exact fun x hx => q' x (q x hx)
    · exact fun x hx => gmap' x (gmap x hx)
    · exact moves
    · exact levels
    · exact archive
  refine ⟨fun x hx => sub e'.1 x (sub e.1 x hx),
    fun i j hj => (order' i j (sub e.1 j hj)).trans (order i j hj),keep,?_⟩
  intro i hi
  have old := (e'.2.1 i (v 7)).mpr (Or.inl ((e.2.1 i (v 7)).mpr (Or.inl hi)))
  exact g.tree.diagram.order.trans i (v 7) (w 7) old (g.tree.diagram.map_bound_l hZF even)

variable {ω c o C₀ S₀ γ Bγ A X K r a f H : M.Domain}

theorem Tg_iteration_run_d.read_l (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    (v : Fin 75 → M.Domain) {i s} (hs : Rd_entry_d i s H) (code : Rt_tuple_d v s) :
    Tg_iteration_d hZF ω c o C₀ S₀ γ Bγ A (fun j => v (j.castAdd 46)) (fun j => v (Fin.natAdd 29 j)) := by
  obtain ⟨w,pack,state⟩ := (h.rows i s hs).1
  exact rt_tuple_inj_l pack code ▸ state

/-- 外部轮号严格小于当轮原树长度；归纳覆盖模型内部的全部自然数。 -/
theorem Tg_iteration_run_d.span_l (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {i s m} (hs : Rd_entry_d i s H) (coord : Rt_coord_d (6 : Fin 75) s m) : M.mem i m := by
  have hw : M.IsOmega ω := by
    obtain ⟨v,code,_⟩ := coord
    exact (h.read_l hZF v hs code).tree.omega
  let ρ : Env M 1 := ⟨fun _ => H,fun _ => H⟩
  let φ : UnarySchema 1 := { body := set[2] ⟪∀ s m,
    ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 2)⌝ₛ,s,⌜(.bound 1 : Term 2)⌝ₛ) →
    ⌜(rt_coord_m (6 : Fin 75))⌝ₚ(s,m) → ⌜(.newest : Term 2)⌝ₛ ∈ m⟫ }
  have sat n : φ.denote ρ n ↔ ∀ s m, Rd_entry_d n s H → Rt_coord_d (6 : Fin 75) s m → M.mem n m := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      rd_entry0_sat_l hZF.1,rt_coord_sat_l hZF.1,Formula.satisfies_mem_iff,Definitional.Term.eval_weaken]; rfl
  have all : ∀ n, M.mem n ω → ∀ s m, Rd_entry_d n s H → Rt_coord_d (6 : Fin 75) s m → M.mem n m := by
    apply hw.induction
    · obtain ⟨B,bs⟩ := ZF.separation_exists_d hZF φ ρ ω
      exact ⟨B,fun n => (bs n).trans (and_congr_right fun _ => sat n)⟩
    · intro z hz s m hs coord
      obtain ⟨v,code,eq⟩ := coord
      have state := h.read_l hZF v hs code
      exact eq ▸ state.tree.diagram.order.ordinal.empty_mem_of_nonempty (ZF.modelsKP hZF)
        ⟨v 7,state.successor.predecessor_mem⟩ hz
    · intro n hn ih j succ t m ht coord
      obtain ⟨s,_,hs⟩ := h.recursion.1.2.1 n hn
      obtain ⟨x,_,v,w,ps,pt,step⟩ := h.steps n j s t succ hs ht
      have old := h.read_l hZF v hs ps
      have bound := ih s (v 6) hs ⟨v,ps,rfl⟩
      have eq := coord.read_l w pt
      obtain ⟨_,_,_,_,_,_,mid,e,e',_⟩ := step
      have sub : M.MemberSubset j (v 6) := by
        intro z hz
        rcases (succ z).mp hz with hz | eq
        · exact old.tree.diagram.order.ordinal.transitive n bound z hz
        · exact (hZF.1.eq_of_same_members z n eq).symm ▸ bound
      have jm : M.mem j (w 7) := Structure.IsOrdinal.mem_of_properSubset hZF.1
        (KP.successor_isOrdinal (ZF.modelsKP hZF) (hw.members_areOrdinals (ZF.modelsKP hZF) n hn) succ)
        mid.diagram.order.ordinal
        ⟨fun z hz => (e.1 z).mpr (Or.inl (sub z hz)),fun eq =>
          KP.mem_irrefl_d (ZF.modelsKP hZF) (v 6) (sub (v 6) ((eq (v 6)).mpr e.1.predecessor_mem))⟩
        (KP.difference_exists_d (ZF.modelsKP hZF) j (w 7))
      exact eq ▸ (e'.1 j).mpr (Or.inl jm)
  exact all i (h.recursion.1.bound_l hs).1 s m hs coord

/-- 原运行自身提供每一有限框架以及共同后继，不另加合并假设。 -/
theorem Tg_iteration_run_d.frames_l (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H) :
    It_frames_d hZF (fun i : Fin 14 => i.castAdd 61) ω c X H := by
  have read {i s} {v : Fin 75 → M.Domain} (hs : Rd_entry_d i s H) (code : Rt_tuple_d v s) := h.read_l hZF v hs code
  have hw : M.IsOmega ω := by
    obtain ⟨z,hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
    obtain ⟨_,_,state⟩ := (h.rows z r (h.recursion.2.1 z hz)).1
    exact state.tree.omega
  refine ⟨h.recursion.1,?_,?_⟩
  · intro i s hs
    obtain ⟨v,code,state⟩ := (h.rows i s hs).1
    obtain ⟨m,succ,hm⟩ := hw.1.2 (v 7) state.finite
    have finite : M.mem (v 6) ω := succ.eq hZF.1 state.successor ▸ hm
    exact ⟨v,code,state.tree,finite,h.span_l hZF hs ⟨v,code,rfl⟩,
      state.levels_function,state.levels,state.request.sequence.2.1⟩
  · have next (i j s t) (succ : M.SuccessorOf j i) (hs : Rd_entry_d i s H) (ht : Rd_entry_d j t H) :
        Tg_run_keep_d (fun i : Fin 14 => i.castAdd 61) s t := by
      obtain ⟨x,_,v,w,ps,pt,step⟩ := h.steps i j s t succ hs ht
      exact ⟨v,w,ps,pt,step.keep_l (v := v) (w := w) hZF (read hs ps) (read ht pt)⟩
    exact fun _ _ _ _ _ _ hs ht ps pt => Tg_run_keep_d.merge_l hZF hw h.recursion.1 next hs ht ps pt

/-- 并树中的每个扩展器由实际有限阶段提供，保留原来的临界点下界。 -/
theorem Tg_iteration_run_d.critical_bound_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H) {Q E : M.Domain}
    (models : ∀ x, M.mem x Q ↔ Tg_run_value_d (9 : Fin 75) H x)
    (moves : ∀ x, M.mem x E ↔ Tg_run_value_d (11 : Fin 75) H x) : It_critical_bound_d I γ Q E := by
  rintro i p κ L F ⟨q,pair,hq⟩ payload
  obtain ⟨v,n,s,hs,code,hq⟩ := (moves q).mp hq
  obtain ⟨a,X,R,⟨r,hp,hr⟩,model,lower⟩ :=
    (h.read_l hZF v hs code).critical i p κ L F ⟨q,pair,hq⟩ payload
  exact ⟨a,X,R,⟨r,hp,(models r).mpr ⟨v,n,s,hs,code,hr⟩⟩,model,lower⟩

/-- 同一原运行的六张并列给出ω长原树、支撑列与完整档案序列。 -/
theorem Tg_iteration_run_d.union_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H) : ∃ U : Fin 6 → M.Domain,
    Tg_iteration_union_d hZF ω c γ H U := by
  have frames := h.frames_l hZF
  obtain ⟨z,hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  obtain ⟨v,code,state⟩ := (h.rows z r (h.recursion.2.1 z hz)).1
  have hw := state.tree.omega
  obtain ⟨U,tree,lf,levels,archive,columns⟩ := frames.union_l hZF hw
  refine ⟨U,⟨tree,h.critical_bound_l hZF (columns 1) (columns 3),lf,levels,
    ⟨hw.isOrdinal (ZF.modelsKP hZF),archive,?_⟩,columns,?_⟩⟩
  · intro i
    constructor
    · intro hi
      obtain ⟨j,succ,hj⟩ := hw.1.2 i hi
      obtain ⟨s,_,hs⟩ := h.recursion.1.2.1 j hj
      obtain ⟨v,code,state⟩ := (h.rows j s hs).1
      have index := (h.rows j s hs).2.read_l v code
      obtain ⟨t,p,pair,hp⟩ := (state.request.sequence.2.2 i).mp (index.symm ▸ succ.predecessor_mem)
      exact ⟨t,p,pair,(columns 5 p).mpr ⟨v,j,s,hs,code,hp⟩⟩
    · rintro ⟨t,p,pair,hp⟩
      obtain ⟨v,j,s,hs,code,hp⟩ := (columns 5 p).mp hp
      have state := h.read_l hZF v hs code
      exact (hw.isOrdinal (ZF.modelsKP hZF)).transitive (v 27) state.request.finite i
        ((state.request.sequence.2.2 i).mpr ⟨t,p,pair,hp⟩)
  · exact fun _ _ _ hs code _ _ hy => frames.order_l hZF columns hs code hy

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原档案索引与真实新增节点的严格次序

第m份档案的节点就是第m轮开始时的原树长。较早档案已经进入较晚轮的实际有限档案，
故其节点严格较小；同一树节点因此只能对应同一档案索引及同一行码。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω c o C₀ S₀ γ Bγ A X K r a f H : M.Domain}

theorem Tg_iteration_run_d.archive_stage_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U)
    {m p s : M.Domain} (row : Tg_archive_row_d M.Domain) (v : Fin 75 → M.Domain)
    (entry : Rd_entry_d m p (U 5)) (tuple : Rt_tuple_d row.values_d p)
    (hs : Rd_entry_d m s H) (code : Rt_tuple_d v s) : row.i = v 6 := by
  have hm := (u.archive.2.2 m).mpr ⟨p,entry⟩
  obtain ⟨j,succ,hj⟩ := u.tree.omega.1.2 m hm
  obtain ⟨t,_,ht⟩ := h.recursion.1.2.1 j hj
  obtain ⟨_,_,v',w,ps,pt,next⟩ := h.steps m j s t succ hs ht
  have eq := rt_tuple_inj_l ps code
  subst v'
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,new,q,index,pack,_,entries⟩ := next
  have added : Rd_entry_d (v 27) q (w 13) := (entries (v 27) q).mpr (Or.inr ⟨rfl,rfl⟩)
  have number : v 27 = m := (h.rows m s hs).2.read_l v code
  have global : Rd_entry_d m q (U 5) := by
    obtain ⟨b,pair,hb⟩ := added
    exact number ▸ (show Rd_entry_d (v 27) q (U 5) from ⟨b,pair,(u.columns 5 b).mpr ⟨w,j,t,ht,pt,hb⟩⟩)
  have eq := u.archive.2.1.2 m q p global entry
  subst q
  have eq := Tg_archive_row_d.eq_l (rt_tuple_inj_l pack tuple)
  subst new
  exact index

theorem Tg_iteration_run_d.archive_order_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U)
    {m n p q : M.Domain} (left right : Tg_archive_row_d M.Domain)
    (hp : Rd_entry_d m p (U 5)) (hq : Rd_entry_d n q (U 5))
    (cp : Rt_tuple_d left.values_d p) (cq : Rt_tuple_d right.values_d q) (mn : M.mem m n) : M.mem left.i right.i := by
  have hn := (u.archive.2.2 n).mpr ⟨q,hq⟩
  obtain ⟨s,_,hs⟩ := h.recursion.1.2.1 n hn
  obtain ⟨v,code,state⟩ := (h.rows n s hs).1
  have number : v 27 = n := (h.rows n s hs).2.read_l v code
  obtain ⟨p',entry⟩ := (state.request.sequence.2.2 m).mp (number.symm ▸ mn)
  have global : Rd_entry_d m p' (U 5) := by
    obtain ⟨b,pair,hb⟩ := entry
    exact ⟨b,pair,(u.columns 5 b).mpr ⟨v,n,s,hs,code,hb⟩⟩
  have eq := u.archive.2.1.2 m p' p global hp
  subst p'
  have links := state.request.links m p left entry cp
  have bound : M.mem left.i (v 6) := (state.successor left.i).mpr (Or.inl links.1)
  exact (h.archive_stage_l hZF u right v hq cq hs code).symm ▸ bound

/-- 同一原节点唯一确定原档案索引和完整外部行码。 -/
theorem Tg_iteration_run_d.archive_unique_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U)
    {m n p q : M.Domain} (left right : Tg_archive_row_d M.Domain)
    (hp : Rd_entry_d m p (U 5)) (hq : Rd_entry_d n q (U 5))
    (cp : Rt_tuple_d left.values_d p) (cq : Rt_tuple_d right.values_d q) (eq : left.i = right.i) : m = n ∧ p = q := by
  have hm := (u.archive.2.2 m).mpr ⟨p,hp⟩
  have hn := (u.archive.2.2 n).mpr ⟨q,hq⟩
  rcases (u.tree.omega.isOrdinal (ZF.modelsKP hZF)).wellOrder.linear.compare m hm n hn with same | mn | nm
  · have same := hZF.1.eq_of_same_members m n same
    subst n
    exact ⟨rfl,u.archive.2.1.2 m p q hp hq⟩
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) right.i (eq ▸ h.archive_order_l hZF u left right hp hq cp cq mn)).elim
  · exact (KP.mem_irrefl_d (ZF.modelsKP hZF) left.i (eq.symm ▸ h.archive_order_l hZF u right left hq hp cq cp nm)).elim

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一原运行的完整复制并历史

先在已实施区间精确恢复原并树的各列，将每份实际有限历史改读为同一原并树的历史。
随后把同一运行的四项复制数据投影为集合函数，沿共尾有限阶段合并全部工作图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {ω c o C₀ S₀ γ Bγ A X K r a f H : M.Domain}

/-- 同一原运行的完整历史、nice工作树及实际根行。 -/
structure Tg_iteration_copy_d (ω c o H : M.Domain) (U W : Fin 6 → M.Domain) : Prop where
  history : Ic_history_d hZF ω (U 0) (U 1) (U 2) (U 3) (U 4) ω (W 0) (U 0) (W 1) (W 2)
  tree : It_pnice_d hZF ω (W 5) ω (U 0) (W 1) (W 2) (W 3) (W 4)
  root : ∃ X B π Z α, Ic_at_d (W 0) o X B π (W 5) Z α ∧ Ic_row_d hZF ω c X B π (W 5) Z α
  operations : ∀ i p, Rd_entry_d i p (W 3) ↔ Ic_operation_d (W 0) (U 3) i p
  includes : ∀ i s (v : Fin 75 → M.Domain), Rd_entry_d i s H → Rt_tuple_d v s →
    M.MemberSubset (v 20) (W 0) ∧ M.MemberSubset (v 22) (W 1) ∧ M.MemberSubset (v 23) (W 2)

/-- 末项之前的原操作和支撑精确恢复，故历史中的否定条件也保持。 -/
theorem Tg_iteration_run_d.original_history_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U)
    {i s} (v : Fin 75 → M.Domain) (hs : Rd_entry_d i s H) (code : Rt_tuple_d v s) :
    Ic_history_d hZF ω (U 0) (U 1) (U 2) (U 3) (U 4) (v 6) (v 20) (v 21) (v 22) (v 23) := by
  have state := h.read_l hZF v hs code
  have keep (b : Fin 6) {i j} (hj : Rd_entry_d i j (v ⟨8+b.val,by omega⟩)) : Rd_entry_d i j (U b) := by
    obtain ⟨p,pair,hp⟩ := hj
    exact ⟨p,pair,(u.columns b p).mpr ⟨v,_,s,hs,code,hp⟩⟩
  have order := u.restriction i s v hs code
  have maps j k g (hk : M.mem k (v 6)) (hg : It_map_d (U 2) j k g) : It_map_d (v 10) j k g := by
    obtain ⟨g',r,pair,hr⟩ := state.tree.diagram.map_l hZF
      ((order j k hk).mp (u.tree.diagram.map_bound_l hZF hg))
    have eq := u.tree.diagram.map_unique_l hZF ⟨r,pair,keep 2 hr⟩ hg
    exact eq ▸ ⟨r,pair,hr⟩
  have moves j p (hj : M.mem j (v 7)) (hp : Rd_entry_d j p (U 3)) : Rd_entry_d j p (v 11) := by
    have no := state.tree.diagram.order.ordinal.mem state.successor.predecessor_mem
    obtain ⟨k,succ⟩ := KP.exists_successor (ZF.modelsKP hZF) j
    have sub : M.MemberSubset k (v 7) := by
      intro x hx
      rcases (succ x).mp hx with hx | eq
      · exact no.transitive j hj x hx
      · exact (hZF.1.eq_of_same_members x j eq).symm ▸ hj
    have hk : M.mem k (v 6) := Structure.IsOrdinal.mem_of_properSubset hZF.1
      (KP.successor_isOrdinal (ZF.modelsKP hZF) (no.mem hj) succ) state.tree.diagram.order.ordinal
      ⟨fun x hx => (state.successor x).mpr (Or.inl (sub x hx)),fun eq =>
        KP.mem_irrefl_d (ZF.modelsKP hZF) (v 7) (sub (v 7) ((eq (v 7)).mpr state.successor.predecessor_mem))⟩
      (KP.difference_exists_d (ZF.modelsKP hZF) k (v 6))
    obtain ⟨q,hq⟩ := (state.tree.move_domain j).mpr ⟨k,hk,succ⟩
    exact u.tree.move_function.2 j q p (keep 3 hq) hp ▸ hq
  have levels j ρ (hj : M.mem j (v 7)) : Rd_entry_d j ρ (U 4) ↔ Rd_entry_d j ρ (v 12) := by
    constructor
    · intro hρ
      obtain ⟨p,κ,F,hp,pay⟩ := (u.levels j ρ).mp hρ
      exact (state.levels j ρ).mpr ⟨p,κ,F,moves j p hj hp,pay⟩
    · exact keep 4
  exact state.history.original_prefix_l hZF state.successor order
    (fun _ _ _ hi => keep 1 hi) maps moves levels

private def Tg_copy_record_d (H n t : M.Domain) : Prop := ∃ v : Fin 75 → M.Domain, ∃ s,
  Rd_entry_d n s H ∧ Rt_tuple_d v s ∧ Rd_quad_d t (v 20) (v 21) (v 22) (v 23)

private def tg_copy_record_m {d} (H n t : Term d) : Formula 1 d :=
  let e : Term d → Term (75+d) := fun x => x.rename (Fin.natAdd 75)
  let v : Fin 75 → Term (75+d) := fun i => .bound (i.castAdd d)
  rb_exists_m (n := 75) (.existsE (.conj (rd_entry0_m (e n).weaken .newest (e H).weaken)
    (.conj (rt_tuple_m (fun i => (v i).weaken) .newest)
      (rd_quad_m (e t).weaken (v 20).weaken (v 21).weaken (v 22).weaken (v 23).weaken))))

@[simp] private theorem tg_copy_record_closed_l {d} (H n t : Term d)
    (hH : H.freeSupport = []) (hn : n.freeSupport = []) (ht : t.freeSupport = []) :
    (tg_copy_record_m H n t).FreeClosed := by
  simp -implicitDefEqProofs [tg_copy_record_m,Definitional.Formula.FreeClosed,hH,hn,ht]
  exact rt_tuple_closed_l _ _ (fun _ => rfl) rfl

private theorem tg_copy_record_sat_l (hE : Extensional M) {d} (ρ : Env M d) (H n t : Term d) :
    Formula.satisfies ρ (tg_copy_record_m H n t) ↔ Tg_copy_record_d (H.eval ρ) (n.eval ρ) (t.eval ρ) := by
  simp only [tg_copy_record_m,Tg_copy_record_d,rb_exists_sat_l,Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff,rd_entry0_sat_l hE,rt_tuple_sat_l hE,rd_quad_sat_l hE,
    Definitional.Term.eval_weaken,rb_old_eval_l,Term.eval_bound,Fin.addCases_left]
  rfl

/-- 沿原运行合并整份复制历史；每个阶段的全部三张工作图都保留。 -/
theorem Tg_iteration_run_d.copy_history_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U) : ∃ J Qw Gw,
    Ic_history_d hZF ω (U 0) (U 1) (U 2) (U 3) (U 4) ω J (U 0) Qw Gw ∧
    ∀ i s (v : Fin 75 → M.Domain), Rd_entry_d i s H → Rt_tuple_d v s →
      M.MemberSubset (v 20) J ∧ M.MemberSubset (v 22) Qw ∧ M.MemberSubset (v 23) Gw := by
  let ρ : Env M 1 := ⟨fun _ => H,fun _ => H⟩
  let φ : BinarySchema 1 := { body := tg_copy_record_m (.bound 2) (.bound 1) .newest }
  have sat n t : φ.denote ρ n t ↔ Tg_copy_record_d H n t := tg_copy_record_sat_l hZF.1 ..
  have total n (hn : M.mem n ω) : ∃ t, φ.denote ρ n t := by
    obtain ⟨s,_,hs⟩ := h.recursion.1.2.1 n hn
    obtain ⟨v,code,_⟩ := (h.rows n s hs).1
    obtain ⟨t,quad⟩ := rd_quad_exists_l (ZF.modelsKP hZF) (v 20) (v 21) (v 22) (v 23)
    exact ⟨t,(sat n t).mpr ⟨v,s,hs,code,quad⟩⟩
  have unique n (_ : M.mem n ω) t t' (ht : φ.denote ρ n t) (ht' : φ.denote ρ n t') : t = t' := by
    obtain ⟨v,s,hs,code,quad⟩ := (sat n t).mp ht
    obtain ⟨w,s',hs',code',quad'⟩ := (sat n t').mp ht'
    have eq := (fn0_function_l (ZF.modelsKP hZF) h.recursion.1).1.2 n s' s hs' hs
    subst s'
    have eq := rt_tuple_inj_l code' code
    subst w
    obtain ⟨p,hp,q,hq,pack⟩ := quad
    obtain ⟨p',hp',q',hq',pack'⟩ := quad'
    have eq := kpair_unique_l M hZF.1 hp' hp
    subst p'
    have eq := kpair_unique_l M hZF.1 hq' hq
    subst q'
    exact kpair_unique_l M hZF.1 pack pack'
  obtain ⟨D,ds⟩ := ZF.exists_functionalImageOn hZF φ ρ ω total unique
  obtain ⟨F,fn,values⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ total unique
    (fun n t hn ht => (ds t).mpr ⟨n,hn,ht⟩)
  have entries n t : Rd_entry_d n t F ↔ M.mem n ω ∧ Tg_copy_record_d H n t :=
    (values n t).trans (and_congr_right fun _ => sat n t)
  have valid n t (ht : Rd_entry_d n t F) : ∃ m J S Qw Gw, M.mem m ω ∧ M.mem n m ∧
      Rd_quad_d t J S Qw Gw ∧ Ic_history_d hZF ω (U 0) (U 1) (U 2) (U 3) (U 4) m J S Qw Gw := by
    obtain ⟨_,v,s,hs,code,quad⟩ := (entries n t).mp ht
    have state := h.read_l hZF v hs code
    obtain ⟨m,succ,hm⟩ := u.tree.omega.1.2 (v 7) state.finite
    exact ⟨v 6,v 20,v 21,v 22,v 23,succ.eq hZF.1 state.successor ▸ hm,
      h.span_l hZF hs ⟨v,code,rfl⟩,quad,h.original_history_l hZF u v hs code⟩
  have chain i j s t (succ : M.SuccessorOf j i) (hs : Rd_entry_d i s F) (ht : Rd_entry_d j t F) : Ic_extend_d s t := by
    obtain ⟨_,v,p,hp,ps,sq⟩ := (entries i s).mp hs
    obtain ⟨_,w,q,hq,pt,tq⟩ := (entries j t).mp ht
    obtain ⟨_,_,v',w',ps',pt',step⟩ := h.steps i j p q succ hp hq
    have eq := rt_tuple_inj_l ps' ps
    subst v'
    have eq := rt_tuple_inj_l pt' pt
    subst w'
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hh,hq,hg,_⟩ := step
    exact ⟨v 20,v 21,v 22,v 23,w 20,w 21,w 22,w 23,sq,tq,hh,hq,hg⟩
  obtain ⟨J,Qw,Gw,hist,kept⟩ := ic_sequence_union_l hZF u.tree.omega u.tree.diagram
    (fn0_of_function_l (ZF.modelsKP hZF) fn) valid chain
  refine ⟨J,Qw,Gw,hist,fun i s v hs code => ?_⟩
  obtain ⟨t,quad⟩ := rd_quad_exists_l (ZF.modelsKP hZF) (v 20) (v 21) (v 22) (v 23)
  have ht := (entries i t).mpr ⟨(h.recursion.1.bound_l hs).1,v,s,hs,code,quad⟩
  exact kept i t (v 20) (v 21) (v 22) (v 23) ht quad

/-- 完整历史的实际复制质量给出nice工作树，原树无需另有nice前提。 -/
theorem Tg_iteration_run_d.copy_l
    (h : Tg_iteration_run_d hZF ω c o C₀ S₀ γ Bγ A X K r a f H)
    {U : Fin 6 → M.Domain} (u : Tg_iteration_union_d hZF ω c γ H U) (empty : ∀ x, ¬ M.mem x o) :
    ∃ W, Tg_iteration_copy_d hZF ω c o H U W := by
  obtain ⟨J,Qw,Gw,hist,kept⟩ := h.copy_history_l hZF u
  obtain ⟨b,N,B,π,z,Z,α,first,hb,_,row⟩ := hist.at_l hZF
    (num_mem_l hZF.1 u.tree.omega (show Num_d 0 o from empty))
  have eq := u.tree.diagram.model_function.2 o b c hb (u.tree.root o empty)
  subst b
  obtain ⟨Ew,Lw,nice,ops⟩ := hist.nice_l hZF u.tree u.levels empty first
  exact ⟨(fun i => [J,Qw,Gw,Ew,Lw,z].get i),hist,nice,⟨N,B,π,Z,α,first,row⟩,ops,kept⟩

end YesMetaZFC.SetTheory.LargeCardinal
