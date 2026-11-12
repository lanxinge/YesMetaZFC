import YesMetaZFC.Model.SetTheory.ClassChoice

/-! # 可定义类状态的统一输入响应表

先对全部状态与输入参数关闭见证，再在实际集合层中一次性选择。
同一响应表服务所有有限局面，因而不会按未来无限对局重新选择。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem ZFC.class_response_l (hZFC : M.Models ZFC) {n} (V : UnarySchema n)
    (φ : UnarySchema (n+2)) (ρ : Env M n) {ω A a} (hw : M.IsOmega ω)
    (step : ∀ s x, V.denote ρ s → M.mem x A → ∃ t, V.denote ρ t ∧ φ.denote ((ρ.push s).push x) t) :
    ∃ X D K, M.mem a X ∧ M.IsCartesianProduct I D X A ∧ M.IsSetFunctionFromTo I K D X ∧
      ∀ s x t p, I.Codes p s x → M.PairMember I p t K → V.denote ρ s →
        V.denote ρ t ∧ φ.denote ((ρ.push s).push x) t := by
  classical
  have hZF := ZFC.models_zf_l hZFC
  let e : Fin n → Term (n+3) := fun i => .bound ⟨i.val+3,by omega⟩
  let ψ : UnarySchema (n+2) := {
    body := .conj (pred_m V e .newest) φ.body
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,e,φ.freeClosed] }
  have sat s x t : ψ.denote ((ρ.push s).push x) t ↔ V.denote ρ t ∧ φ.denote ((ρ.push s).push x) t := by
    simp only [ψ,UnarySchema.denote,Formula.satisfies_conj_iff,pred_sat_l]
    rfl
  let v : Fin (n+2) → M.Domain := Fin.cases a (Fin.cases A ρ.bound)
  obtain ⟨B,_,bs⟩ := ZF.finite_params_l I hZF hw v
  have hb i : M.mem (v i) B := (bs _).mpr ⟨i,rfl⟩
  obtain ⟨α,X,rank,_,bx,closed⟩ := ZF.lr_closed_layer_l I hZF hw [⟨n+2,ψ⟩] B
  have tr := v_transitive_l I rank
  have ax : M.mem a X := tr B bx a (hb 0)
  have alphabet : M.mem A X := tr B bx A (hb 1)
  have params i : M.mem (ρ.bound i) X := tr B bx _ (hb i.succ.succ)
  have total s x (hs : M.mem s X) (hx : M.mem x A) (hv : V.denote ρ s) :
      ∃ t, M.mem t X ∧ ψ.denote ((ρ.push s).push x) t := by
    obtain ⟨t,ht⟩ := step s x hv hx
    exact closed ⟨n+2,ψ⟩ (by simp) ((ρ.push s).push x)
      (Fin.cases (tr A alphabet x hx) (Fin.cases hs params)) ⟨t,(sat s x t).mpr ht⟩
  obtain ⟨D,product⟩ := ZF.exists_cartesianProduct hZF I X A
  let aenv := ρ.push a
  let e' : Fin n → Term (n+5) := fun i => .bound ⟨i.val+5,by omega⟩
  let f : Fin (n+2) → Term (n+5) := Fin.cases .newest (Fin.cases (.bound 1) e')
  let θ : BinarySchema (n+1) := {
    body := .existsE (.existsE (.conj
    (𝒞.code (.bound 3) (.bound 1) .newest)
    (.disj (.conj (pred_m V e' (.bound 1)) (pred_m ψ f (.bound 2)))
      (.conj (.neg (pred_m V e' (.bound 1))) (Formula.extensionalEq (.bound 2) (.bound 4))))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,e',f,Fin.forall_fin_succ] }
  have read p t : θ.denote aenv p t ↔ ∃ s x, I.Codes p s x ∧
      ((V.denote ρ s ∧ ψ.denote ((ρ.push s).push x) t) ∨ (¬ V.denote ρ s ∧ t = a)) := by
    have env s x : (⟨fun i => (f i).eval ((((aenv.push p).push t).push s).push x),
        ((((aenv.push p).push t).push s).push x).free⟩ : Env M (n+2)) = (ρ.push s).push x := by
      rw [Env.mk.injEq]
      exact ⟨funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))),rfl⟩
    simp only [θ,BinarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      I.realizes,Formula.satisfies_disj_iff,pred_sat_l,Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1,env]
    rfl
  obtain ⟨K,fn,values⟩ := ZFC.uniformize_formula_l I hZFC θ aenv (X := D) (Y := X) (by
    intro p hp
    obtain ⟨s,hs,x,hx,pair⟩ := (product p).mp hp
    by_cases hv : V.denote ρ s
    · obtain ⟨t,ht,valid⟩ := total s x hs hx hv
      exact ⟨t,ht,(read p t).mpr ⟨s,x,pair,Or.inl ⟨hv,valid⟩⟩⟩
    · exact ⟨a,ax,(read p a).mpr ⟨s,x,pair,Or.inr ⟨hv,rfl⟩⟩⟩)
  refine ⟨X,D,K,ax,product,fn,fun s x t p pair hp hv => ?_⟩
  obtain ⟨s',x',pair',ht⟩ := (read p t).mp (values p t hp)
  obtain ⟨rfl,rfl⟩ := I.injective pair pair'
  exact ht.elim (fun h => (sat s x t).mp h.2) (fun h => (h.1 hv).elim)

end YesMetaZFC.SetTheory
