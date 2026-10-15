import YesMetaZFC.SetTheory.LargeCardinal.TypeGameProjection
import YesMetaZFC.SetTheory.Descriptive.TreePullback
import YesMetaZFC.SetTheory.FunctionSpaceAlgebra

/-! # 6.7 的无约束坐标：实际字母映射与二坐标投影

删除三元字母的中坐标 (a,(n,γ))↦(a,γ)。该映射的逆像树保留任意中坐标，
二坐标投影直接量化原树分支，不以三坐标游戏充当定义。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M)

def Tv_drop_value_d (p q : M.Domain) : Prop := ∃ a b c v,
  (I).Codes p a v ∧ (I).Codes v b c ∧ (I).Codes q a c

def tv_drop_value_m {d} (p q : Term d) : Formula 1 d := set[d] ⟪∃ a b c v,
  ⌜kpair_convention_l.code⌝ₚ(⌜p⌝ₛ,a,v) ∧ ⌜kpair_convention_l.code⌝ₚ(v,b,c) ∧ ⌜kpair_convention_l.code⌝ₚ(⌜q⌝ₛ,a,c)⟫
derive_free_closed tv_drop_value_m

theorem tv_drop_value_sat_l {d} (ρ : Env M d) (p q : Term d) :
    Formula.satisfies ρ (tv_drop_value_m p q) ↔ Tv_drop_value_d I (p.eval ρ) (q.eval ρ) := by
  simp only [tv_drop_value_m, Tv_drop_value_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    I.satisfies_code_iff, Definitional.Term.eval_weaken]; rfl

theorem Tv_drop_value_d.unique_l {p q r : M.Domain} (h : Tv_drop_value_d I p q) (k : Tv_drop_value_d I p r) : q = r := by
  obtain ⟨a, b, c, v, ap, bc, ac⟩ := h
  obtain ⟨a', b', c', v', ap', bc', ac'⟩ := k
  obtain ⟨rfl, rfl⟩ := I.injective ap ap'
  obtain ⟨rfl, rfl⟩ := I.injective bc bc'
  exact I.unique ac ac'

def Tv_drop_d (Y Z d : M.Domain) : Prop := M.IsSetFunctionFromTo I d Y Z ∧
  ∀ p q, M.PairMember I p q d ↔ M.mem p Y ∧ Tv_drop_value_d I p q

theorem tv_drop_l (hZF : M.Models ZF) {A B Γ P Y Z : M.Domain}
    (prod : M.IsCartesianProduct I P B Γ) (letters : M.IsCartesianProduct I Y A P)
    (pair : M.IsCartesianProduct I Z A Γ) : ∃ d, Tv_drop_d I Y Z d := by
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => Y⟩
  let φ : BinarySchema 0 := { body := tv_drop_value_m (.bound 1) .newest }
  have sat p q : φ.denote ρ p q ↔ Tv_drop_value_d I p q := tv_drop_value_sat_l I ..
  obtain ⟨d, fn, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := Y) (target := Z) (by
    intro p hp
    obtain ⟨a, _, v, hv, ap⟩ := (letters p).mp hp
    obtain ⟨b, _, c, _, bc⟩ := (prod v).mp hv
    obtain ⟨q, ac⟩ := I.total a c
    exact ⟨q, (sat p q).mpr ⟨a, b, c, v, ap, bc, ac⟩⟩)
    (fun _ _ _ _ h k => ((sat ..).mp h).unique_l I ((sat ..).mp k)) (by
      intro p q hp h
      obtain ⟨a, b, c, v, ap, bc, ac⟩ := (sat p q).mp h
      obtain ⟨a', ha, v', hv, ap'⟩ := (letters p).mp hp
      obtain ⟨rfl, rfl⟩ := I.injective ap ap'
      obtain ⟨b', _, c', hc, bc'⟩ := (prod v).mp hv
      obtain ⟨rfl, rfl⟩ := I.injective bc bc'
      exact (pair q).mpr ⟨a, ha, c, hc, ac⟩)
  exact ⟨d, fn, fun p q => (graph p q).trans (and_congr_right fun _ => sat p q)⟩

/-- 二坐标树体的第一投影，分支和第一坐标均为所在模型的实际函数图。 -/
def Tp_projection_d (ω A Y F T x : M.Domain) : Prop := ∃ q,
  M.IsSetFunctionFromTo I q ω Y ∧ Branch_d F T q ∧ M.IsLeftFunctionProjection I x q ω A

def tp_projection_m {d} (ω A Y F T x : Term d) : Formula 1 d := .existsE (.conj
  (Formula.isFunctionFromTo kpair_convention_l .newest ω.weaken Y.weaken) (.conj
    (branch_m F.weaken T.weaken .newest)
    (Formula.isLeftFunctionProjection kpair_convention_l x.weaken .newest ω.weaken A.weaken)))

@[simp] theorem tp_projection_closed_l {d} (ω A Y F T x : Term d)
    (hw : ω.freeSupport = []) (ha : A.freeSupport = []) (hy : Y.freeSupport = [])
    (hf : F.freeSupport = []) (ht : T.freeSupport = []) (hx : x.freeSupport = []) :
    (tp_projection_m ω A Y F T x).FreeClosed := by
  simp -implicitDefEqProofs [tp_projection_m, Formula.isLeftFunctionProjection, Definitional.Formula.FreeClosed, hw, ha, hy, hf, ht, hx]

theorem tp_projection_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A Y F T x : Term d) :
    Formula.satisfies ρ (tp_projection_m ω A Y F T x) ↔ Tp_projection_d I
      (ω.eval ρ) (A.eval ρ) (Y.eval ρ) (F.eval ρ) (T.eval ρ) (x.eval ρ) := by
  simp only [tp_projection_m, Tp_projection_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_isFunctionFromTo_iff I hE, branch_sat_l,
    Formula.satisfies_isLeftFunctionProjection_iff I hE, Definitional.Term.eval_weaken]; rfl

theorem tp_right_l (hZF : M.Models ZF) {D A Γ Y q : M.Domain} (pair : M.IsCartesianProduct I Y A Γ)
    (fq : M.IsSetFunctionFromTo I q D Y) : ∃ g, M.IsRightFunctionProjection I g q D Γ := by
  let ρ : Env M 1 := ⟨fun _ => q, fun _ => q⟩
  let φ := BinarySchema.rightFunctionProjectionValue kpair_convention_l
  have sat i z : φ.denote ρ i z ↔ ∃ v x, M.PairMember I i v q ∧ (I).Codes v x z :=
    Formula.denote_rightFunctionProjectionValue_iff I ..
  obtain ⟨g, fg, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := D) (target := Γ) (by
    intro i hi
    obtain ⟨v, hv, iv⟩ := fq.2.2 i hi
    obtain ⟨x, _, z, _, c⟩ := (pair v).mp hv
    exact ⟨z, (sat i z).mpr ⟨v, x, iv, c⟩⟩) (by
      intro i _ z z' iz iz'
      obtain ⟨v, x, iv, c⟩ := (sat i z).mp iz
      obtain ⟨v', x', iv', c'⟩ := (sat i z').mp iz'
      have eq := fq.1.2 i v v' iv iv'; subst v'
      exact (I.injective c c').2) (by
        intro i z _ iz
        obtain ⟨v, x, iv, c⟩ := (sat i z).mp iz
        obtain ⟨x', _, z', hz, c'⟩ := (pair v).mp (fq.output_mem_of_pairMember iv)
        exact (I.injective c c').2.symm ▸ hz)
  exact ⟨g, fg, fun i z => (graph i z).trans ((and_congr_right fun _ => sat i z).trans
    ⟨And.right, fun h => ⟨h.elim fun _ h => h.elim fun _ h => fq.input_mem_of_pairMember h.1, h⟩⟩)⟩

section Branch
variable (hZF : M.Models ZF)
local notation "J" => kp_pair_l (ZF.modelsKP hZF)

/-- 删除无约束坐标保持投影；反向在该坐标插入常值零列。 -/
theorem tv_projection_l {ω A Γ P Y Z F G T S d x : M.Domain} (hw : M.IsOmega ω)
    (prod : M.IsCartesianProduct J P ω Γ) (letters : M.IsCartesianProduct J Y A P)
    (pair : M.IsCartesianProduct J Z A Γ) (space : Fseq_space_d J ω Y F)
    (target : Fseq_space_d J ω Z G) (drop : Tv_drop_d J Y Z d) (pull : Tr_pull_d J d F T S)
    (fx : M.IsSetFunctionFromTo J x ω A) :
    Tg_projection_d hZF ω Y F S x ↔ Tp_projection_d J ω A Z G T x := by
  constructor
  · rintro ⟨q, t, g, fq, branch, _, _, join⟩
    -- 删除中坐标得到原树分支；逐项核对第一坐标仍是原对局。
    have fq := fn0_function_l (ZF.modelsKP hZF) fq
    obtain ⟨r, fr, qr⟩ := ZF.fseq_compose_l J hZF drop.1 fq
    have first i v (iv : M.PairMember J i v r) : ∃ a z, M.PairMember J i a x ∧ (J).Codes v a z := by
      obtain ⟨p, ip, pv⟩ := (qr.2 i v).mp iv
      obtain ⟨a, b, z, u, ap, bz, az⟩ := ((drop.2 p v).mp pv).2
      obtain ⟨a', b', z', u', p', ia, _, _, bu, au, ip'⟩ := join.2 i (fq.input_mem_of_pairMember ip)
      have eq := fq.1.2 i p' p ip' ip; subst p'
      obtain ⟨rfl, rfl⟩ := (J).injective au ap
      obtain ⟨rfl, rfl⟩ := (J).injective bu bz
      exact ⟨_, _, ia, az⟩
    refine ⟨r, fr, (pull.branch_l J hZF hw drop.1 space target fq qr).mp branch, fx, fun i a => ⟨?_, ?_⟩⟩
    · intro ia
      obtain ⟨v, _, iv⟩ := fr.2.2 i (fx.input_mem_of_pairMember ia)
      obtain ⟨a', z, ia', az⟩ := first i v iv
      have eq := fx.1.2 i a' a ia' ia; subst a'
      exact ⟨v, z, iv, az⟩
    · rintro ⟨v, z, iv, az⟩
      obtain ⟨a', z', ia', az'⟩ := first i v iv
      exact (J).injective az' az |>.1 ▸ ia'
  · rintro ⟨q, fq, branch, left⟩
    -- 从二坐标分支实际分离标签列，插入常值自然数列并合成为三坐标分支。
    obtain ⟨g, right⟩ := tp_right_l J hZF pair fq
    obtain ⟨z, _, hz⟩ := hw.1.1
    obtain ⟨t, ft, _⟩ := ZF.exists_constantFunction hZF J (source := ω) hz
    obtain ⟨P', Y', r, prod', letters', fr, join⟩ := tg_join_exists_l J hZF left.1 ft right.1
    have eq := hZF.1.eq_of_same_members P' P fun v => (prod' v).trans (prod v).symm; subst P'
    have eq := hZF.1.eq_of_same_members Y' Y fun v => (letters' v).trans (letters v).symm; subst Y'
    have compatible i p v (ip : M.PairMember J i p r) (iv : M.PairMember J i v q) : Tv_drop_value_d J p v := by
      obtain ⟨a, b, c, u, p', ia, _, ic, bc, au, ip'⟩ := join.2 i (fr.input_mem_of_pairMember ip)
      have eq := fr.1.2 i p' p ip' ip; subst p'
      obtain ⟨a', _, c', _, ac⟩ := (pair v).mp (fq.output_mem_of_pairMember iv)
      have ia' := (left.2 i a').mpr ⟨v, c', iv, ac⟩
      have ic' := (right.2 i c').mpr ⟨v, a', iv, ac⟩
      have eq := left.1.1.2 i a' a ia' ia; subst a'
      have eq := right.1.1.2 i c' c ic' ic; subst c'
      exact ⟨a, b, c, u, au, bc, ac⟩
    have rq : Fseq_recode_d J d r q := by
      refine ⟨fq.1.1, fun i v => ⟨?_, ?_⟩⟩
      · intro iv
        obtain ⟨p, hp, ip⟩ := fr.2.2 i (fq.input_mem_of_pairMember iv)
        exact ⟨p, ip, (drop.2 p v).mpr ⟨hp, compatible i p v ip iv⟩⟩
      · rintro ⟨p, ip, pv⟩
        obtain ⟨v', _, iv'⟩ := fq.2.2 i (fr.input_mem_of_pairMember ip)
        have pv' := (drop.2 p v').mpr ⟨fr.output_mem_of_pairMember ip, compatible i p v' ip iv'⟩
        exact drop.1.1.2 p v' v pv' pv ▸ iv'
    exact ⟨r, t, g, fn0_of_function_l (ZF.modelsKP hZF) fr,
      (pull.branch_l J hZF hw drop.1 space target fr rq).mpr branch,
      ⟨ft.1, ft.2.1⟩, ⟨right.1.1, right.1.2.1⟩, join⟩

end Branch
end YesMetaZFC.SetTheory.LargeCardinal
