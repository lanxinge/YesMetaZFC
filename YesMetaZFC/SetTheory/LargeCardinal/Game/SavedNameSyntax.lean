import YesMetaZFC.Model.SetTheory.Relations.RecordImage
import YesMetaZFC.Model.SetTheory.Internal.FiniteRecordRelative

/-! # 原关系存档的五十四个回答坐标

存档码属于产生回答的模型；背景只保存对象码及所属关系。外延性与完整
元组共同确定每个坐标，历史中的比较因此不需要把记录解释成背景有序对。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

/-- 外部档案原行：产生结点、模型、原回答、根图及其工作复制，均保留原对象码。 -/
structure Tg_archive_row_d (α : Type u) where
  i : α
  c : α
  X : α
  R : α
  w : α
  η : α
  C : α
  L : α
  U : α
  q : α
  p : α
  A : α
  π : α

def Tg_archive_row_d.values_d {α : Type u} (s : Tg_archive_row_d α) : Fin 13 → α :=
  fun j => [s.i,s.c,s.X,s.R,s.w,s.η,s.C,s.L,s.U,s.q,s.p,s.A,s.π].get j

def tg_saved_code0_m : Formula 1 59 := .conj
  (rf_ext_m (𝒞 := kpair_convention_l) (.bound 54) (.bound 55))
  (rf_tuple_m (𝒞 := kpair_convention_l) (.bound 54) (.bound 55)
    (Fin.cases (.bound 56) (Fin.cases (.bound 57) (fun i : Fin 54 => .bound (i.castAdd 5)))) (.bound 58))

theorem tg_saved_code0_closed_l : tg_saved_code0_m.FreeClosed := by
  simp -implicitDefEqProofs [tg_saved_code0_m, Definitional.Formula.FreeClosed]
  exact rf_tuple_closed_l _ _ _ _ rfl rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) rfl

def Tg_saved_code_d (Y R ω V q : M.Domain) (v : Fin 54 → M.Domain) : Prop :=
  Formula.satisfies (⟨Fin.addCases (m := 54) (n := 5) v (fun i : Fin 5 => [Y,R,ω,V,q].get i), fun _ => q⟩ : Env M 59) tg_saved_code0_m

def tg_saved_code_m {d} (Y R ω V q : Term d) (v : Fin 54 → Term d) : Formula 1 d :=
  tg_saved_code0_m.bind (Fin.addCases (m := 54) (n := 5) v (fun i : Fin 5 => [Y,R,ω,V,q].get i))

@[simp] theorem tg_saved_code_closed_l {d} (Y R ω V q : Term d) (v : Fin 54 → Term d)
    (hY : Y.freeSupport = []) (hR : R.freeSupport = []) (hw : ω.freeSupport = [])
    (hV : V.freeSupport = []) (hq : q.freeSupport = []) (hv : ∀ i, (v i).freeSupport = []) :
    (tg_saved_code_m Y R ω V q v).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr tg_saved_code0_closed_l
  intro i
  refine Fin.addCases (m := 54) (n := 5) (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.addCases_left] using hv j
  · simp only [Fin.addCases_right]
    exact Fin.cases hY (Fin.cases hR (Fin.cases hw (Fin.cases hV (Fin.cases hq (fun k => Fin.elim0 k))))) j

theorem tg_saved_code_sat_l {d} (ρ : Env M d) (Y R ω V q : Term d) (v : Fin 54 → Term d) :
    Formula.satisfies ρ (tg_saved_code_m Y R ω V q v) ↔
      Tg_saved_code_d (Y.eval ρ) (R.eval ρ) (ω.eval ρ) (V.eval ρ) (q.eval ρ) (fun i => (v i).eval ρ) := by
  rw [tg_saved_code_m, Formula.satisfies_bind, Tg_saved_code_d]
  apply Formula.closed_env_l _ tg_saved_code0_closed_l
  funext i
  exact Fin.addCases (m := 54) (n := 5) (fun j => by
    simp only [Definitional.Env.substitute, Fin.addCases_left]
    rfl)
    (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))) i

theorem tg_saved_code_read_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {Y R ω V q : M.Domain} {v : Fin 54 → M.Domain} :
    Tg_saved_code_d Y R ω V q v ↔ Rf_ext_d I Y R ∧ Rf_tuple_d I Y R (Fin.cases ω (Fin.cases V v)) q := by
  simp only [Tg_saved_code_d, tg_saved_code0_m, Formula.satisfies_conj_iff, rf_ext_sat_l I hE, rf_tuple_sat_l I]
  have row : (fun i : Fin 56 =>
      ((Fin.cases (.bound 56) (Fin.cases (.bound 57) (fun j : Fin 54 => .bound (j.castAdd 5))) i : Term 59).eval
        (⟨Fin.addCases (m := 54) (n := 5) v (fun j : Fin 5 => [Y,R,ω,V,q].get j), fun _ => q⟩ : Env M 59))) =
      Fin.cases ω (Fin.cases V v) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => by
      change Fin.addCases _ _ (j.castAdd 5) = v j
      exact Fin.addCases_left ..)) i
  rw [row]
  rfl

/-- 同一存档码只给出一份坐标表，比较仍在原关系中进行。 -/
theorem Tg_saved_code_d.inj_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {Y R ω V ω' V' q : M.Domain} {v w : Fin 54 → M.Domain}
    (a : Tg_saved_code_d Y R ω V q v) (b : Tg_saved_code_d Y R ω' V' q w) :
    (Fin.cases ω (Fin.cases V v) : Fin 56 → M.Domain) = Fin.cases ω' (Fin.cases V' w) := by
  obtain ⟨ext, a⟩ := (tg_saved_code_read_l I hE).mp a
  exact a.inj_l I ext ((tg_saved_code_read_l I hE).mp b).2

theorem Tg_saved_code_d.values_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {Y R ω V q : M.Domain} {v : Fin 54 → M.Domain} (h : Tg_saved_code_d Y R ω V q v) :
    ∀ i, M.mem (v i) Y := by
  obtain ⟨m, _⟩ := ((tg_saved_code_read_l I hE).mp h).2
  exact fun i => m i.succ.succ.succ

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原档案中的树名与同一个根对象

树名取自同一完整54项存档的第19项，沿该行自己的真实根图解释。
原档案不随当前模型改写，新增行则由本次实际回答的坐标证明其根像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Tg_saved_name_d (S X R w U q p : M.Domain) : Prop :=
  ∀ v : Fin 54 → M.Domain, Tg_saved_code_d X R w U q v → M.PairMember I S (v 19) p

theorem Tg_saved_name_d.of_code_l (hE : Extensional M)
    {S X R w U q p : M.Domain} {v : Fin 54 → M.Domain}
    (code : Tg_saved_code_d X R w U q v) (name : M.PairMember I S (v 19) p) :
    Tg_saved_name_d I S X R w U q p := by
  intro u pack
  have eq : v 19 = u 19 := congrFun (code.inj_l I hE pack) 21
  exact eq ▸ name

theorem Tg_archive_row_d.eq_l {a b : Tg_archive_row_d M.Domain} (h : a.values_d = b.values_d) : a = b := by
  cases a; cases b
  congr 1 <;> first
    | exact congrFun h 0 | exact congrFun h 1 | exact congrFun h 2
    | exact congrFun h 3 | exact congrFun h 4 | exact congrFun h 5
    | exact congrFun h 6 | exact congrFun h 7 | exact congrFun h 8
    | exact congrFun h 9 | exact congrFun h 10 | exact congrFun h 11 | exact congrFun h 12

def Tg_archive_names_d (S H : M.Domain) : Prop :=
  ∀ m r, ∀ a : Tg_archive_row_d M.Domain, M.PairMember I m r H → Rt_tuple_d a.values_d r →
    Tg_saved_name_d I S a.X a.R a.w a.U a.q a.p

theorem Tg_archive_names_d.push_l {S H H' m r : M.Domain} {a : Tg_archive_row_d M.Domain}
    (old : Tg_archive_names_d I S H) (code : Rt_tuple_d a.values_d r)
    (name : Tg_saved_name_d I S a.X a.R a.w a.U a.q a.p)
    (entries : ∀ k s, M.PairMember I k s H' ↔ M.PairMember I k s H ∨ k = m ∧ s = r) :
    Tg_archive_names_d I S H' := by
  intro k s b hs cb
  rcases (entries k s).mp hs with hs | ⟨rfl,rfl⟩
  · exact old k s b hs cb
  · exact (Tg_archive_row_d.eq_l (rt_tuple_inj_l cb code)).symm ▸ name

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 原保存码中根树名的一阶编码

完整五十四项码的每次读取都必须给出同一根图中的树名。此公共编码供
原档案与工作复制档案直接使用，不依赖任何复制历史句法。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def tg_saved_name_m {d} (S X R w U q p : Term d) : Formula 1 d :=
  let r : Term d → Term (54+d) := fun t => t.rename (Fin.natAdd 54)
  rb_forall_m (.imp (tg_saved_code_m (r X) (r R) (r w) (r U) (r q)
    (fun i => .bound (i.castAdd d)))
    (Formula.orderedPairMem kpair_convention_l (r S) (.bound ⟨19,by omega⟩) (r p)))

@[simp] theorem tg_saved_name_closed_l {d} (S X R w U q p : Term d)
    (hS : S.freeSupport = []) (hX : X.freeSupport = []) (hR : R.freeSupport = [])
    (hw : w.freeSupport = []) (hU : U.freeSupport = []) (hq : q.freeSupport = [])
    (hp : p.freeSupport = []) : (tg_saved_name_m S X R w U q p).FreeClosed := by
  simp -implicitDefEqProofs [tg_saved_name_m,Definitional.Formula.FreeClosed,hS,hX,hR,hw,hU,hq,hp]

theorem tg_saved_name_sat_l (I : kpair_convention_l.Interpretation M) {d} (ρ : Env M d)
    (S X R w U q p : Term d) : Formula.satisfies ρ (tg_saved_name_m S X R w U q p) ↔
      Tg_saved_name_d I (S.eval ρ) (X.eval ρ) (R.eval ρ) (w.eval ρ) (U.eval ρ) (q.eval ρ) (p.eval ρ) := by
  simp only [tg_saved_name_m,Tg_saved_name_d,rb_forall_sat_l,Formula.satisfies_imp_iff,
    tg_saved_code_sat_l,Formula.satisfies_orderedPairMem_iff I,rb_old_eval_l,Term.eval_bound,
    Fin.addCases_left]
  rfl

end YesMetaZFC.SetTheory.LargeCardinal
