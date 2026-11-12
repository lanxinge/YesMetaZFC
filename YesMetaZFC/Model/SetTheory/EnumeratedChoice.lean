import YesMetaZFC.Model.SetTheory.DependentChoice
import YesMetaZFC.SetTheory.FunctionCoordinates
import YesMetaZFC.SetTheory.Definitional.Project.Predicate

/-! # 随实际参数列变化的内部依赖选择

在 (轮号,状态) 上使用原 DC，随后用实际一阶公式归纳识别轮号坐标。
所得状态列逐轮消费给定的参数图，保留原初值；内部 ω 不要求外部标准。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem Dc_d.parameter_l (hZF : M.Models ZF) {ω X Y e p₀ : M.Domain} (hw : M.IsOmega ω)
    (dc : Dc_d I ω) {n} (φ : UnarySchema (n+2)) (ρ : Env M n)
    (fe : M.IsSetFunctionFromTo I e ω X) (hp₀ : M.mem p₀ Y)
    (total : ∀ p a, M.mem p Y → M.mem a X → ∃ q, M.mem q Y ∧ φ.denote ((ρ.push p).push a) q) :
    ∃ f, M.IsSetFunctionFromTo I f ω Y ∧
      (∀ o, (∀ x, ¬ M.mem x o) → M.PairMember I o p₀ f) ∧
      ∀ i j p q, M.SuccessorOf j i → M.PairMember I i p f → M.PairMember I j q f →
        ∀ a, M.PairMember I i a e → φ.denote ((ρ.push p).push a) q := by
  obtain ⟨S,prod⟩ := ZF.exists_cartesianProduct hZF I ω Y
  let η := ρ.push e
  let σ : Fin (n+2) → Term (n+8) := Fin.cases .newest (Fin.cases (.bound 3)
    (fun i => (.bound i : Term n).weaken.weaken.weaken.weaken.weaken.weaken.weaken.weaken))
  have closedσ (i) : (σ i).freeSupport = [] := Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) i
  let ψ : BinarySchema (n+1) := {
    body := .existsE <| .existsE <| .existsE <| .existsE <| .existsE <|
      .conj (𝒞.code (.bound 6) (.bound 4) (.bound 3)) <|
        .conj (𝒞.code (.bound 5) (.bound 2) (.bound 1)) <|
          .conj (Formula.isSuccessor (.bound 2) (.bound 4)) <|
            .conj (Formula.orderedPairMem 𝒞 (.bound 4) .newest (.bound 7)) <|
              pred_m φ σ (.bound 1)
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,closedσ] }
  have env s t i p j q a : (⟨fun v => (σ v).eval (((((((η.push s).push t).push i).push p).push j).push q).push a),
      (((((((η.push s).push t).push i).push p).push j).push q).push a).free⟩ : Env M (n+2)) =
      (ρ.push p).push a := by
    rw [Env.mk.injEq]
    refine ⟨funext (Fin.cases rfl (Fin.cases ?_ (fun v => ?_))),rfl⟩
    · simp only [σ,Fin.cases_succ,Fin.cases_zero,Term.eval_bound_three_push,Term.eval_bound_two_push,
        Term.eval_bound_one_push,Term.eval_bound_zero_push]
      rfl
    · simp only [σ,Fin.cases_succ,Definitional.Term.eval_weaken]
      rfl
  have sat s t : ψ.denote η s t ↔ ∃ i p j q a, I.Codes s i p ∧ I.Codes t j q ∧
      M.SuccessorOf j i ∧ M.PairMember I i a e ∧ φ.denote ((ρ.push p).push a) q := by
    simp only [ψ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      I.realizes,Formula.satisfies_isSuccessor_iff,Formula.satisfies_orderedPairMem_iff I,pred_sat_l M,
      Term.eval_bound_seven_push,Term.eval_bound_six_push,Term.eval_bound_five_push,Term.eval_bound_four_push,
      Term.eval_bound_three_push,Term.eval_bound_two_push,Term.eval_bound_one_push,Term.eval_bound_zero_push,env]
    rfl
  obtain ⟨R,_,read⟩ := ZF.exists_setRelationOn_of_denote hZF I ψ η S
  have edges s t := (read s t).trans (and_congr_right fun _ => and_congr_right fun _ => sat s t)
  obtain ⟨o,empty,ho⟩ := hw.1.1
  obtain ⟨s₀,pair₀⟩ := I.total o p₀
  obtain ⟨G,fg,zero,chain⟩ := dc S R s₀ ((prod s₀).mpr ⟨o,ho,p₀,hp₀,pair₀⟩) (by
    intro s hs
    obtain ⟨i,hi,p,hp,pair⟩ := (prod s).mp hs
    obtain ⟨a,ha,ia⟩ := fe.2.2 i hi
    obtain ⟨q,hq,pq⟩ := total p a hp ha
    obtain ⟨j,succ,hj⟩ := hw.1.2 i hi
    obtain ⟨t,paired⟩ := I.total j q
    have ht := (prod t).mpr ⟨j,hj,q,hq,paired⟩
    exact ⟨t,ht,(edges s t).mpr ⟨hs,ht,i,p,j,q,a,pair,paired,succ,ia,pq⟩⟩)
  let ξ : Env M 1 := ⟨fun _ => G,fun _ => G⟩
  let χ : UnarySchema 1 := { body := .forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
    (.existsE (𝒞.code (.bound 1) (.bound 2) .newest))) }
  have test i : χ.denote ξ i ↔ ∀ s, M.PairMember I i s G → ∃ p, I.Codes s i p := by
    simp only [χ,UnarySchema.denote,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
      Formula.satisfies_orderedPairMem_iff I,Formula.satisfies_exists_iff,I.realizes]
    rfl
  have number : ∀ i, M.mem i ω → ∀ s, M.PairMember I i s G → ∃ p, I.Codes s i p := by
    apply hw.induction
    · obtain ⟨C,cut⟩ := ZF.separation_exists_d hZF χ ξ ω
      exact ⟨C,fun i => (cut i).trans (and_congr_right fun _ => test i)⟩
    · intro b eb s bs
      have bo := hZF.1.eq_of_same_members b o (fun x => iff_of_false (eb x) (empty x))
      have ss := fg.1.2 b s s₀ bs (zero b eb)
      exact ⟨p₀,ss.symm ▸ bo.symm ▸ pair₀⟩
    · intro i hi ih j succ t jt
      obtain ⟨s,_,is⟩ := fg.2.2 i hi
      obtain ⟨p,sp⟩ := ih s is
      obtain ⟨_,_,i',p',j',q,a,sp',tq,succ',_⟩ := (edges s t).mp (chain i j s t succ is jt)
      have eq := (I.injective sp sp').1
      subst i'
      exact ⟨q,succ'.eq hZF.1 succ ▸ tq⟩
  obtain ⟨_,f,_,ff,coords⟩ := ZF.function_coords_l I hZF fg
    (fun s hs => ((prod s).mp hs).elim fun i h => h.2.elim fun p hp => ⟨i,p,h.1,hp.1,hp.2⟩)
  have point i p (ip : M.PairMember I i p f) : ∃ s, M.PairMember I i s G ∧ I.Codes s i p := by
    have hi := ff.input_mem_of_pairMember ip
    obtain ⟨s,_,is⟩ := fg.2.2 i hi
    obtain ⟨q,sq⟩ := number i hi s is
    exact ⟨s,is,ff.1.2 i q p (coords i s i q is sq).2 ip ▸ sq⟩
  refine ⟨f,ff,?_,?_⟩
  · intro b eb
    have bo := hZF.1.eq_of_same_members b o (fun x => iff_of_false (eb x) (empty x))
    exact bo.symm ▸ (coords o s₀ o p₀ (zero o empty) pair₀).2
  · intro i j p q succ ip jq a ia
    obtain ⟨s,is,sp⟩ := point i p ip
    obtain ⟨t,jt,tq⟩ := point j q jq
    obtain ⟨_,_,i',p',j',q',a',sp',tq',_,ia',pq⟩ := (edges s t).mp (chain i j s t succ is jt)
    obtain ⟨eqi,eqp⟩ := I.injective sp' sp
    obtain ⟨eqj,eqq⟩ := I.injective tq' tq
    subst i' p' j' q'
    exact fe.1.2 i a' a ia' ia ▸ pq

end YesMetaZFC.SetTheory
