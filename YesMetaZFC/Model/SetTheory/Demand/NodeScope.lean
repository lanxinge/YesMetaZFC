import YesMetaZFC.Model.SetTheory.Internal.FiniteSource
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.Model.SetTheory.Internal.Theory
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.Model.SetTheory.Types.Embedding
import YesMetaZFC.SetTheory.Descriptive.Game.GameShift
import YesMetaZFC.SetTheory.Descriptive.Coding.Prefix

/-! # 内部有限指定坐标组的完整集合程序

选择集合只决定哪些原变量进入该组，不给变量规定标签次序。沿模型的
内部 ω 编译有限析取，再同时检查集合的两个包含方向。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

private def td_build_m {d} (ω n F m G u : Term d) : Formula 1 d := set[d] ⟪
  ⌜sfm_m (𝒞 := 𝒞)⌝ₚ(⌜ω⌝ₛ,⌜m⌝ₛ,⌜G⌝ₛ) ∧
  ⌜Formula.isRestriction 𝒞⌝ₚ(⌜F⌝ₛ,⌜G⌝ₛ,⌜n⌝ₛ) ∧ ⌜n⌝ₛ ⊆ ⌜m⌝ₛ ∧ ⌜u⌝ₛ ∈ ⌜m⌝ₛ⟫

@[simp] private theorem td_build_closed_l {d} (ω n F m G u : Term d)
    (hw : ω.freeSupport = []) (hn : n.freeSupport = []) (hF : F.freeSupport = [])
    (hm : m.freeSupport = []) (hG : G.freeSupport = []) (hu : u.freeSupport = []) :
    (td_build_m (𝒞 := 𝒞) ω n F m G u).FreeClosed := by
  simp -implicitDefEqProofs [td_build_m,Definitional.Formula.FreeClosed,hw,hn,hF,hm,hG,hu]

private theorem td_build_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω n F m G u : Term d) :
    Formula.satisfies ρ (td_build_m (𝒞 := 𝒞) ω n F m G u) ↔
      Sbuild_d I (ω.eval ρ) (n.eval ρ) (F.eval ρ) (m.eval ρ) (G.eval ρ) (u.eval ρ) := by
  simp only [td_build_m,Formula.satisfies_conj_iff,sfm_sat_l I hE,
    Formula.satisfies_isRestriction_iff I,Formula.satisfies_subset_iff,Formula.satisfies_mem_iff]
  exact ⟨fun ⟨a,b,c,d⟩ => ⟨a,b,c,d⟩,fun h => ⟨h.program,h.cut,h.span,h.root⟩⟩

def Td_any_d (ω A b n m G u : M.Domain) : Prop := ∀ X R E f x,
  M.IsFunctionSpace I E ω X → M.mem f E → M.PairMember I b x f →
    (Ssat_d I X R E G m u f ↔ ∃ i, M.mem i n ∧ M.mem i A ∧ M.PairMember I i x f)

def td_any_m {d} (ω A b n m G u : Term d) : Formula 1 d := set[d] ⟪∀ X R E f x,
  ⌜Formula.isFunctionSpace 𝒞⌝ₚ(E,⌜ω⌝ₛ,X) → f ∈ E → ⌜Formula.orderedPairMem 𝒞⌝ₚ(⌜b⌝ₛ,x,f) →
    (⌜ssat_m (𝒞 := 𝒞)⌝ₚ(X,R,E,⌜G⌝ₛ,⌜m⌝ₛ,⌜u⌝ₛ,f) ↔
      (∃ i ∈ ⌜n⌝ₛ, i ∈ ⌜A⌝ₛ ∧ ⌜Formula.orderedPairMem 𝒞⌝ₚ(i,x,f)))⟫

@[simp] theorem td_any_closed_l {d} (ω A b n m G u : Term d)
    (hw : ω.freeSupport = []) (hA : A.freeSupport = []) (hb : b.freeSupport = [])
    (hn : n.freeSupport = []) (hm : m.freeSupport = []) (hG : G.freeSupport = []) (hu : u.freeSupport = []) :
    (td_any_m (𝒞 := 𝒞) ω A b n m G u).FreeClosed := by
  simp -implicitDefEqProofs [td_any_m,Formula.isFunctionSpace,Definitional.Formula.FreeClosed,hw,hA,hb,hn,hm,hG,hu]

theorem td_any_sat_l (hE : Extensional M) {d} (ρ : Env M d) (ω A b n m G u : Term d) :
    Formula.satisfies ρ (td_any_m (𝒞 := 𝒞) ω A b n m G u) ↔
      Td_any_d I (ω.eval ρ) (A.eval ρ) (b.eval ρ) (n.eval ρ) (m.eval ρ) (G.eval ρ) (u.eval ρ) := by
  simp only [td_any_m,Td_any_d,Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,
    Formula.satisfies_isFunctionSpace_iff I hE,Formula.satisfies_mem_iff,Formula.satisfies_orderedPairMem_iff I,
    Formula.satisfies_iff_iff,ssat_sat_l I hE,Formula.satisfies_existsMem_iff,Formula.satisfies_conj_iff,
    Definitional.Term.eval_weaken]
  rfl

theorem td_any_build_l (hZF : M.Models ZF) {ω A b n n₀ F₀ : M.Domain}
    (hω : M.IsOmega ω) (hb : M.mem b ω) (hn : M.mem n ω) (base : Sfm_d I ω n₀ F₀) :
    ∃ m G u, Sbuild_d I ω n₀ F₀ m G u ∧ Td_any_d I ω A b n m G u := by
  let ρ : Env M 5 := ⟨fun i => [b,A,ω,n₀,F₀].get i,fun _ => ω⟩
  let φ : UnarySchema 5 := { body := .existsE (.existsE (.existsE (.conj
    (td_build_m (𝒞 := 𝒞) (.bound 6) (.bound 7) (.bound 8) (.bound 2) (.bound 1) .newest)
      (td_any_m (𝒞 := 𝒞) (.bound 6) (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest)))) }
  have sat k : φ.denote ρ k ↔ ∃ m G u, Sbuild_d I ω n₀ F₀ m G u ∧ Td_any_d I ω A b k m G u := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
      td_build_sat_l I hZF.1,td_any_sat_l I hZF.1]
    rfl
  apply (sat n).mp
  apply hω.induction (fun k => φ.denote ρ k) (ZF.separation_exists_d hZF φ ρ ω) ?_ ?_ n hn
  · intro z hz
    obtain ⟨m,G,add,eq⟩ := sfm_eq_l I hZF hω base hb hb
    obtain ⟨l,H,u,neg,read⟩ := sfm_neg_l I hZF hω add.program add.root
    refine (sat z).mpr ⟨l,H,u,add.comp I neg,fun X R E f x hE hf hx => ?_⟩
    exact (read X R E f hf).trans ((not_congr (eq X R E f x x hE hf hx hx)).trans
      (iff_of_false (fun h => h rfl) (fun ⟨i,hi,_⟩ => hz i hi)))
  · intro k hk ih l succ
    obtain ⟨m,G,u,prog,all⟩ := (sat k).mp ih
    by_cases hkA : ¬ M.mem k A
    · refine (sat l).mpr ⟨m,G,u,prog,fun X R E f x hE hf hx => (all X R E f x hE hf hx).trans ?_⟩
      exact ⟨fun ⟨i,hi,hiA,hx⟩ => ⟨i,(succ i).mpr (Or.inl hi),hiA,hx⟩,
        fun ⟨i,hi,hiA,hx⟩ => ⟨i,((succ i).mp hi).elim id
          (fun eq => (hkA (hZF.1.eq_of_same_members i k eq ▸ hiA)).elim),hiA,hx⟩⟩
    have hkA : M.mem k A := Classical.byContradiction hkA
    obtain ⟨m₁,G₁,add,eq⟩ := sfm_eq_l I hZF hω prog.program hb hk
    obtain ⟨m₂,G₂,v,disj,both⟩ := sfm_or_l I hZF hω add.program (add.span u prog.root) add.root
    refine (sat l).mpr ⟨m₂,G₂,v,(prog.comp I add).comp I disj,fun X R E f x hE hf hx => ?_⟩
    obtain ⟨y,_,hy⟩ := ((hE f).mp hf).2.2 k hk
    have old := (add.sat_l I hZF prog.program prog.root X R E f).symm.trans (all X R E f x hE hf hx)
    refine (both X R E f hf).trans ((or_congr old (eq X R E f x y hE hf hx hy)).trans ⟨?_,?_⟩)
    · rintro (⟨i,hi,hiA,hx⟩ | eq)
      · exact ⟨i,(succ i).mpr (Or.inl hi),hiA,hx⟩
      · exact ⟨k,succ.predecessor_mem,hkA,eq.symm ▸ hy⟩
    · rintro ⟨i,hi,hiA,hx⟩
      rcases (succ i).mp hi with hi | eq
      · exact Or.inl ⟨i,hi,hiA,hx⟩
      · exact Or.inr (((hE f).mp hf).1.2 k x y (hZF.1.eq_of_same_members i k eq ▸ hx) hy)

def Td_group_d (A n f g : M.Domain) : Prop := ∀ x,
  M.mem x g ↔ ∃ i, M.mem i n ∧ M.mem i A ∧ M.PairMember I i x f

theorem td_group_build_l (hZF : M.Models ZF) {ω A n b p n₀ F₀ : M.Domain}
    (hω : M.IsOmega ω) (hn : M.mem n ω) (hb : M.mem b ω) (hp : M.mem p ω)
    (hbp : M.mem b p) (np : M.MemberSubset n p) (base : Sfm_d I ω n₀ F₀) :
    ∃ m G u, Sbuild_d I ω n₀ F₀ m G u ∧ ∀ c X R E f g,
      Smem_d I c X R → M.TransitiveSet X → M.IsFunctionSpace I E ω X → M.mem f E →
      M.PairMember I b g f → (Ssat_d I X R E G m u f ↔ Td_group_d I A n f g) := by
  obtain ⟨m₀,G₀,u₀,prog,any⟩ := td_any_build_l I hZF (A := A) hω hp hn base
  obtain ⟨m₁,G₁,add,rel⟩ := sfm_rel_l I hZF hω prog.program hp hb
  obtain ⟨m₂,G₂,u₂,iff,both⟩ := sfm_iff_l I hZF hω add.program add.root (add.span u₀ prog.root)
  obtain ⟨m,G,u,all,quant⟩ := sfm_all_l I hZF hω iff.program hp iff.root
  refine ⟨m,G,u,((prog.comp I add).comp I iff).comp I all,fun c X R E f g model trans hE hf hg => ?_⟩
  have fn := (hE f).mp hf
  have hG := fn.output_mem_of_pairMember hg
  have body x f₁ (hx : M.mem x X) (update : Senv_update_d I f p x f₁) :
      Ssat_d I X R E G₂ m₂ u₂ f₁ ↔ (M.mem x g ↔ ∃ i, M.mem i n ∧ M.mem i A ∧ M.PairMember I i x f) := by
    have hf₁ := (hE f₁).mpr (update.function_l I fn hp hx)
    have px := (update.2 p x).mpr (Or.inl ⟨rfl,rfl⟩)
    have agree := Senv_update_d.agree_l I update (KP.mem_irrefl_d (ZF.modelsKP hZF) p)
    have bg := (agree b g hbp).mp hg
    have old := (add.sat_l I hZF prog.program prog.root X R E f₁).symm.trans (any X R E f₁ x hE hf₁ px)
    have member : M.PairMember I x g R ↔ M.mem x g := (model.2 x g).trans
      ((and_iff_right hx).trans (and_iff_right hG))
    have entries : (∃ i, M.mem i n ∧ M.mem i A ∧ M.PairMember I i x f₁) ↔
        ∃ i, M.mem i n ∧ M.mem i A ∧ M.PairMember I i x f :=
      exists_congr fun i => and_congr_right fun hi => and_congr_right fun _ => (agree i x (np i hi)).symm
    exact (both X R E f₁ hf₁).trans (iff_congr ((rel X R E f₁ x g hE hf₁ px bg).trans member) (old.trans entries))
  refine (quant X R E f hE hf).trans ⟨?_,?_⟩
  · intro all x
    by_cases hx : M.mem x X
    · obtain ⟨f₁,update,_⟩ := senv_update_exists_l I hZF fn hp hx
      exact (body x f₁ hx update).mp (all x f₁ hx update)
    · exact iff_of_false (fun h => hx (trans g hG x h))
        (fun ⟨_,_,_,h⟩ => hx (fn.output_mem_of_pairMember h))
  · exact fun all x f₁ hx update => (body x f₁ hx update).mpr (all x)

end YesMetaZFC.SetTheory.Internal

/-! ## 两组原变量形成同一完整节点的内部程序

两组集合分别绑定为对象；原元组仍逐变量读取。程序精确描述两组的
值集合及它们与实际原局组成的同一树节点，不规定组内标签排列。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_node_build_l {ω e l b A B : M.Domain} (hω : M.IsOmega ω)
    (hl : M.mem l ω) (hb : M.mem b ω) (he : M.mem e l) (lb : M.MemberSubset l b)
    (σ : Fin 2 → M.Domain) (hσ : ∀ i, M.mem (σ i) b) :
    ∃ a m G u, Sformula_d I ω a m G u ∧ ∀ c X R f S s k,
      Smem_d I c X R → M.TransitiveSet X → M.IsSetFunctionFromTo I f ω X →
      Rd_entry_d e S f → Rd_entry_d (σ 0) s f → Rd_entry_d (σ 1) k f →
      (Satisfies_d I ω c a f ↔ ∃ g h, M.mem g X ∧ M.mem h X ∧
        Td_group_d I A l f g ∧ Td_group_d I B l f h ∧ Tg_node_d I k S s g h) := by
  obtain ⟨p,bp,hp⟩ := hω.1.2 b hb
  obtain ⟨q,pq,hq⟩ := hω.1.2 p hp
  have up {i} (hi : M.mem i b) : M.mem i p := (bp i).mpr (Or.inl hi)
  have uq {i} (hi : M.mem i b) : M.mem i q := (pq i).mpr (Or.inl (up hi))
  have lq : M.MemberSubset l q := fun i hi => uq (lb i hi)
  obtain ⟨z,hz⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have empty : Sfm_d I ω z z := ⟨num_mem_l hZF.1 hω (show Num_d 0 z from hz),
    Structure.IsSequenceOfLength.empty I hz,fun _ _ h => h.elim fun t ht => (hz t ht.2).elim⟩
  obtain ⟨m₁,G₁,u₁,one,read₁⟩ := td_group_build_l I hZF (A := A) hω hl hb hq
    ((pq b).mpr (Or.inl bp.predecessor_mem)) lq empty
  obtain ⟨m₂,G₂,u₂,two,read₂⟩ := td_group_build_l I hZF (A := B) hω hl hp hq pq.predecessor_mem lq one.program
  let φ : Formula 1 5 := tg_node_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4)
  have closed : φ.FreeClosed := tg_node_m_freeClosed _ _ _ _ _ rfl rfl rfl rfl rfl
  let v : Fin 5 → M.Domain := fun i => [σ 1,e,σ 0,b,p].get i
  have hv : ∀ i, M.mem (v i) q := Fin.cases (uq (hσ 1))
    (Fin.cases (uq (lb e he)) (Fin.cases (uq (hσ 0))
      (Fin.cases ((pq b).mpr (Or.inl bp.predecessor_mem))
        (Fin.cases pq.predecessor_mem (fun i => Fin.elim0 i)))))
  obtain ⟨m₃,G₃,u₃,compile,truth⟩ := source_compile_core_l I hZF hω (source_core_l φ)
    (source_core_closed_l φ closed) v hq hv two.program
  obtain ⟨m₄,G₄,u₄,bothNode,both⟩ := sfm_and_l I hZF hω compile.program (compile.span u₂ two.root) compile.root
  have prior := (two.comp I compile).comp I bothNode
  obtain ⟨m₅,G₅,u₅,bothAll,all⟩ := sfm_and_l I hZF hω bothNode.program (prior.span u₁ one.root) bothNode.root
  obtain ⟨m₆,G₆,u₆,ex₂,second⟩ := sfm_ex_l I hZF hω bothAll.program hp bothAll.root
  obtain ⟨m,G,u,ex₁,first⟩ := sfm_ex_l I hZF hω ex₂.program hb ex₂.root
  obtain ⟨a,code⟩ := (I).total G u
  have form : Sformula_d I ω a m G u := ⟨code,ex₁.program,ex₁.root⟩
  refine ⟨a,m,G,u,form,fun c X R f S s k model trans ff fS fs fk => ?_⟩
  obtain ⟨E,hE⟩ := ZF.exists_functionSpace hZF I ω X
  have hf := (hE f).mpr ff
  let nx : Nonempty {x // M.mem x X} := ⟨⟨S,ff.output_mem_of_pairMember fS⟩⟩
  have body g h (hg : M.mem g X) (hh : M.mem h X) f₁ f₂
      (ug : Senv_update_d I f b g f₁) (uh : Senv_update_d I f₁ p h f₂) :
      Ssat_d I X R E G₅ m₅ u₅ f₂ ↔
        Td_group_d I A l f g ∧ Td_group_d I B l f h ∧ Tg_node_d I k S s g h := by
    have ff₁ := ug.function_l I ff hb hg
    have ff₂ := uh.function_l I ff₁ hp hh
    have hf₂ := (hE f₂).mpr ff₂
    have agree₁ := ug.agree_l I (KP.mem_irrefl_d (ZF.modelsKP hZF) b)
    have agree₂ := uh.agree_l I (KP.mem_irrefl_d (ZF.modelsKP hZF) p)
    have same i x (hi : M.mem i b) : Rd_entry_d i x f ↔ Rd_entry_d i x f₂ :=
      (agree₁ i x hi).trans (agree₂ i x (up hi))
    have bg := (agree₂ b g bp.predecessor_mem).mp ((ug.2 b g).mpr (Or.inl ⟨rfl,rfl⟩))
    have ph := (uh.2 p h).mpr (Or.inl ⟨rfl,rfl⟩)
    have groups C y : Td_group_d I C l f₂ y ↔ Td_group_d I C l f y :=
      forall_congr' fun x => iff_congr Iff.rfl (exists_congr fun i => and_congr_right fun hi =>
        and_congr_right fun _ => (same i x (lb i hi)).symm)
    have firstRead := (prior.sat_l I hZF one.program one.root X R E f₂).symm.trans
      ((read₁ c X R E f₂ g model trans hE hf₂ bg).trans (groups A g))
    have secondRead := (compile.sat_l I hZF two.program two.root X R E f₂).symm.trans
      ((read₂ c X R E f₂ h model trans hE hf₂ ph).trans (groups B h))
    let ρ : Env (rt_model_l X nx) 5 := ⟨fun i =>
      [⟨k,ff.output_mem_of_pairMember fk⟩,⟨S,ff.output_mem_of_pairMember fS⟩,
        ⟨s,ff.output_mem_of_pairMember fs⟩,⟨g,hg⟩,⟨h,hh⟩].get i,fun _ => ⟨g,hg⟩⟩
    let η : Env (smdl_structure_l I (R := R) model.1.2.1) 5 := ⟨ρ.bound,ρ.free⟩
    have values : ∀ i, Rd_entry_d (v i) (η.bound i).val f₂ := Fin.cases ((same (σ 1) k (hσ 1)).mp fk)
      (Fin.cases ((same e S (lb e he)).mp fS) (Fin.cases ((same (σ 0) s (hσ 0)).mp fs)
        (Fin.cases bg (Fin.cases ph (fun i => Fin.elim0 i)))))
    have nodeRead := (truth X R model.1.2.1 E hE f₂ hf₂ η values).trans ((source_core_sat_l φ η).trans
      ((smem_formula_l I model nx φ ρ).symm.trans
        (tg_node_source_l trans nx (ZF.modelsKP hZF).1 (KP.exists_pair (ZF.modelsKP hZF)) ρ _ _ _ _ _)))
    exact (all X R E f₂ hf₂).trans (and_congr firstRead
      ((both X R E f₂ hf₂).trans (and_congr secondRead nodeRead)))
  refine (satisfies_decode_l I hZF.1 model.1 form hE).trans ((first X R E f hf).trans ⟨?_,?_⟩)
  · rintro ⟨g,f₁,hg,ug,valid⟩
    obtain ⟨h,f₂,hh,uh,truth⟩ := (second X R E f₁ ((hE f₁).mpr (ug.function_l I ff hb hg))).mp valid
    exact ⟨g,h,hg,hh,(body g h hg hh f₁ f₂ ug uh).mp truth⟩
  · rintro ⟨g,h,hg,hh,truth⟩
    obtain ⟨f₁,ug,ff₁⟩ := senv_update_exists_l I hZF ff hb hg
    obtain ⟨f₂,uh,_⟩ := senv_update_exists_l I hZF ff₁ hp hh
    exact ⟨g,f₁,hg,ug,(second X R E f₁ ((hE f₁).mpr ff₁)).mpr
      ⟨h,f₂,hh,uh,(body g h hg hh f₁ f₂ ug uh).mpr truth⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 7.1 双组完整节点的实际类型查询

原奇数组与偶数组分别读作值集合；只排除首位树坐标，不按标签排序。
实际程序同时约束两个集合并检查同一树节点，完整类型读取保留这份精确分组。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}}

def Td_groups_d (I : kpair_convention_l.Interpretation M) (ω e l r a b : M.Domain) : Prop :=
  (∀ p, M.mem p a ↔ ∃ i, M.mem i l ∧ i ≠ e ∧ ¬ Gm_even_d I ω i ∧ M.PairMember I i p r) ∧
  (∀ p, M.mem p b ↔ ∃ i, M.mem i l ∧ i ≠ e ∧ Gm_even_d I ω i ∧ M.PairMember I i p r)

theorem Td_groups_d.cover_l {I : kpair_convention_l.Interpretation M} {ω e l r a b : M.Domain}
    (h : Td_groups_d I ω e l r a b) :
    ∀ p, (M.mem p a ∨ M.mem p b) ↔ ∃ i, M.mem i l ∧ i ≠ e ∧ M.PairMember I i p r := by
  intro p
  constructor
  · intro hp
    exact hp.elim (fun ha => ((h.1 p).mp ha).elim fun i hi => ⟨i,hi.1,hi.2.1,hi.2.2.2⟩)
      (fun hb => ((h.2 p).mp hb).elim fun i hi => ⟨i,hi.1,hi.2.1,hi.2.2.2⟩)
  · rintro ⟨i,hi,ne,ip⟩
    exact (Classical.em (Gm_even_d I ω i)).elim
      (fun even => Or.inr ((h.2 p).mpr ⟨i,hi,ne,even,ip⟩))
      (fun odd => Or.inl ((h.1 p).mpr ⟨i,hi,ne,odd,ip⟩))

def Td_node_query_d (I : kpair_convention_l.Interpretation M) (ω e n l U D s k q : M.Domain) : Prop :=
  M.mem q D ∧ ∀ c X R r δ T S, Smem_d I c X R → M.TransitiveSet X →
    Tt_realized_d I ω c X R n r δ U D T → Rd_entry_d e S r →
      (M.mem q T ↔ ∃ a b, M.mem a X ∧ M.mem b X ∧
        (∀ p, (M.mem p a ∨ M.mem p b) ↔ ∃ i, M.mem i l ∧ i ≠ e ∧ M.PairMember I i p r) ∧
        Tg_node_d I k S s a b ∧ Td_groups_d I ω e l r a b)

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tt_demand_node_query_l {ω e n l U D s k : M.Domain} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hl : M.mem l n) (he : M.mem e l) (pool : Tt_pool_d I ω n U D)
    (hs : M.mem s U) (hk : M.mem k U) : ∃ q, Td_node_query_d I ω e n l U D s k q := by
  let ρ : Env M 2 := ⟨Fin.cases e (fun _ => ω),fun _ => ω⟩
  let φ : UnarySchema 2 := { body := set[3] ⟪¬ (⌜(.newest : Term 3)⌝ₛ = ⌜(.bound 1 : Term 3)⌝ₛ) ∧
    ⌜(gm_even_m (𝒞 := kpair_convention_l))⌝ₚ(⌜(.bound 2 : Term 3)⌝ₛ,⌜(.newest : Term 3)⌝ₛ)⟫ }
  let ψ : UnarySchema 2 := { body := set[3] ⟪¬ (⌜(.newest : Term 3)⌝ₛ = ⌜(.bound 1 : Term 3)⌝ₛ) ∧
    ¬ ⌜(gm_even_m (𝒞 := kpair_convention_l))⌝ₚ(⌜(.bound 2 : Term 3)⌝ₛ,⌜(.newest : Term 3)⌝ₛ)⟫ }
  have ev i : φ.denote ρ i ↔ i ≠ e ∧ Gm_even_d I ω i := by
    simp only [φ,UnarySchema.denote,Formula.satisfies_conj_iff,Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1,gm_even_sat_l I hZF.1]
    rfl
  have od i : ψ.denote ρ i ↔ i ≠ e ∧ ¬ Gm_even_d I ω i := by
    simp only [ψ,UnarySchema.denote,Formula.satisfies_conj_iff,Formula.satisfies_neg_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1,gm_even_sat_l I hZF.1]
    rfl
  obtain ⟨O,hO⟩ := ZF.separation_exists_d hZF ψ ρ l
  obtain ⟨E,hE⟩ := ZF.separation_exists_d hZF φ ρ l
  have odd i : M.mem i O ↔ M.mem i l ∧ i ≠ e ∧ ¬ Gm_even_d I ω i :=
    (hO i).trans (and_congr_right fun _ => od i)
  have even i : M.mem i E ↔ M.mem i l ∧ i ≠ e ∧ Gm_even_d I ω i :=
    (hE i).trans (and_congr_right fun _ => ev i)
  obtain ⟨N,C,names,sequences,product⟩ := pool
  obtain ⟨b,σ,hb,nb,bound,_,columns⟩ := tt_column_build_l hZF hω hn 2
  let a : Fin 2 → M.Domain := Fin.cases s (fun _ => k)
  have ha : ∀ i, M.mem (a i) U := Fin.cases hs (fun _ => hk)
  obtain ⟨v,hv⟩ := Classical.axiomOfChoice (fun i => (I).total (a i) (a i))
  obtain ⟨J,column,original,params⟩ := columns U N names v
    (fun i => (names (v i)).mpr (Or.inr (Or.inr ⟨a i,ha i,hv i⟩)))
  have ord := hω.members_areOrdinals (ZF.modelsKP hZF) n hn
  have ln : M.MemberSubset l n := ord.transitive l hl
  obtain ⟨f,m,G,u,form,node⟩ := td_node_build_l hZF (A := O) (B := E) hω
    (hω.transitive (ZF.modelsKP hZF) n hn l hl) hb he (fun i hi => nb i (ln i hi)) σ bound
  obtain ⟨z,code⟩ := sc_num_exists_l I hZF hω form
  obtain ⟨q,cq⟩ := (I).total z J
  have hz := sc_num_natural_l I hZF hω code
  have hq := (product q).mpr ⟨z,hz,J,(sequences J).mpr ⟨b,hb,column⟩,cq⟩
  refine ⟨q,hq,fun c X R r δ T S model trans type rS => ?_⟩
  obtain ⟨r₁,assign,fr₁⟩ := tn_assign_exists_l hZF ord type.tuple type.point type.constants names
    (fn0_of_function_l (ZF.modelsKP hZF) column)
  obtain ⟨f₁,fill,ff₁⟩ := senv_fill_exists_l I hZF (fn0_function_l (ZF.modelsKP hZF) fr₁) type.point
  have value i j x (hj : Rd_entry_d i j J) (hx : Tn_value_d n r δ j x) : Rd_entry_d i x f₁ :=
    (fill.2 i x).mpr ⟨hω.transitive (ZF.modelsKP hZF) b hb i (column.input_mem_of_pairMember hj),
      Or.inl ⟨column.input_mem_of_pairMember hj,(assign.2 i x).mpr ⟨j,hj,hx⟩⟩⟩
  have vars i x (hx : Rd_entry_d i x r) : Rd_entry_d i x f₁ :=
    value i i x (original i (type.tuple.bound_l hx).1) (Or.inl hx)
  have same i x (hi : M.mem i n) : Rd_entry_d i x r ↔ Rd_entry_d i x f₁ := by
    refine ⟨vars i x,fun hx => ?_⟩
    obtain ⟨y,_,hy⟩ := type.tuple.2.1 i hi
    exact ff₁.1.2 i y x (vars i y hy) hx ▸ hy
  have constants i : Rd_entry_d (σ i) (a i) f₁ := value (σ i) (v i) (a i) (params i) (Or.inr (Or.inr (hv i)))
  have groups g h : (Td_group_d I O l f₁ g ∧ Td_group_d I E l f₁ h) ↔ Td_groups_d I ω e l r g h := by
    have first g : Td_group_d I O l f₁ g ↔
        ∀ p, M.mem p g ↔ ∃ i, M.mem i l ∧ i ≠ e ∧ ¬ Gm_even_d I ω i ∧ Rd_entry_d i p r := by
      apply forall_congr'
      intro p
      apply iff_congr Iff.rfl
      apply exists_congr
      intro i
      exact ⟨fun ⟨hi,ho,ip⟩ => ⟨hi,((odd i).mp ho).2.1,((odd i).mp ho).2.2,(same i p (ln i hi)).mpr ip⟩,
        fun ⟨hi,ne,par,ip⟩ => ⟨hi,(odd i).mpr ⟨hi,ne,par⟩,(same i p (ln i hi)).mp ip⟩⟩
    have second h : Td_group_d I E l f₁ h ↔
        ∀ p, M.mem p h ↔ ∃ i, M.mem i l ∧ i ≠ e ∧ Gm_even_d I ω i ∧ Rd_entry_d i p r := by
      apply forall_congr'
      intro p
      apply iff_congr Iff.rfl
      apply exists_congr
      intro i
      exact ⟨fun ⟨hi,he,ip⟩ => ⟨hi,((even i).mp he).2.1,((even i).mp he).2.2,(same i p (ln i hi)).mpr ip⟩,
        fun ⟨hi,ne,par,ip⟩ => ⟨hi,(even i).mpr ⟨hi,ne,par⟩,(same i p (ln i hi)).mp ip⟩⟩
    exact and_congr (first g) (second h)
  have decoded := (type.truth q).trans ((and_iff_right hq).trans
    ((tt_query_decode_l I (ZF.modelsKP hZF) cq hz hb column.2.1 assign fill).trans
      ((sc_sat_decode_l I hZF hω code).trans
        (node c X R f₁ S s k model trans ff₁ (vars e S rS) (constants 0) (constants 1)))))
  refine decoded.trans (exists_congr fun g => exists_congr fun h => and_congr_right fun _ => and_congr_right fun _ => ?_)
  exact ⟨fun ⟨ga,gb,node⟩ => let gs := (groups g h).mp ⟨ga,gb⟩; ⟨gs.cover_l,node,gs⟩,
    fun ⟨_,node,gs⟩ => ⟨((groups g h).mpr gs).1,((groups g h).mpr gs).2,node⟩⟩

/-- 给定真实有限元组和同树节点，直接生成含该完整节点查询的实际类型。 -/
theorem tt_demand_node_realize_l
    {ω e n l U s k c X R r δ S a b : M.Domain} (hω : M.IsOmega ω)
    (hn : M.mem n ω) (hl : M.mem l n) (he : M.mem e l)
    (model : Smem_d I c X R) (trans : M.TransitiveSet X) (tuple : Fn0_d n X r)
    (point : M.mem δ X) (constants : M.MemberSubset U X) (hs : M.mem s U) (hk : M.mem k U)
    (rS : Rd_entry_d e S r) (ha : M.mem a X) (hb : M.mem b X)
    (node : Tg_node_d I k S s a b) (groups : Td_groups_d I ω e l r a b) :
    ∃ D T q, Tt_realized_d I ω c X R n r δ U D T ∧
      Td_node_query_d I ω e n l U D s k q ∧ M.mem q T := by
  obtain ⟨D,T,pool,truth,_⟩ := tt_type_exists_l I hZF hω c n r δ U
  have actual : Tt_realized_d I ω c X R n r δ U D T := ⟨model.1,hn,tuple,point,constants,pool,truth⟩
  obtain ⟨q,query⟩ := tt_demand_node_query_l hZF hω hn hl he pool hs hk
  exact ⟨D,T,q,actual,query,(query.2 c X R r δ T S model trans actual rS).mpr
    ⟨a,b,ha,hb,groups.cover_l,node,groups⟩⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 固定 demanding 节点查询的一阶证书

两组标签分别保留奇、偶槽的完整值集合。查询公式量化同一模型上的
全部完整类型，同时保留两组覆盖、三图节点与各组精确对应。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}}

def td_groups_m {d} (ω e q r a b : Term d) : Formula 1 d := set[d] ⟪
  (∀ p, p ∈ ⌜a⌝ₛ ↔ ∃ i ∈ ⌜q⌝ₛ, ¬ (i = ⌜e⌝ₛ) ∧
    ¬ ⌜(gm_even_m (𝒞 := kpair_convention_l))⌝ₚ(⌜ω⌝ₛ,i) ∧
      ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i,p,⌜r⌝ₛ)) ∧
  (∀ p, p ∈ ⌜b⌝ₛ ↔ ∃ i ∈ ⌜q⌝ₛ, ¬ (i = ⌜e⌝ₛ) ∧
    ⌜(gm_even_m (𝒞 := kpair_convention_l))⌝ₚ(⌜ω⌝ₛ,i) ∧
      ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i,p,⌜r⌝ₛ))⟫

derive_free_closed td_groups_m

theorem td_groups_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M)
    {d} (ρ : Env M d) (ω e q r a b : Term d) :
    Formula.satisfies ρ (td_groups_m ω e q r a b) ↔
      Td_groups_d I (ω.eval ρ) (e.eval ρ) (q.eval ρ) (r.eval ρ) (a.eval ρ) (b.eval ρ) := by
  simp only [td_groups_m,Td_groups_d,Formula.satisfies_conj_iff,Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,Formula.satisfies_existsMem_iff,
    Formula.satisfies_neg_iff,Formula.satisfies_extensionalEq_iff_eq hE,
    gm_even_sat_l I hE,Formula.satisfies_orderedPairMem_iff I,Definitional.Term.eval_weaken]
  rfl

def td_node_query0_m : Formula 1 9 :=
  let ω := Term.bound 0; let e := Term.bound 1; let n := Term.bound 2
  let l := Term.bound 3; let U := Term.bound 4; let D := Term.bound 5
  let s := Term.bound 6; let k := Term.bound 7; let q := Term.bound 8
  set[9] ⟪⌜q⌝ₛ ∈ ⌜D⌝ₛ ∧
  (∀ c X R r δ T S, ⌜smem_m (𝒞 := kpair_convention_l)⌝ₚ(c,X,R) → ⌜Formula.isTransitive⌝ₚ(X) →
    ⌜tt_realized_m⌝ₚ(⌜ω⌝ₛ,c,X,R,⌜n⌝ₛ,r,δ,⌜U⌝ₛ,⌜D⌝ₛ,T) → ⌜rd_entry0_m⌝ₚ(⌜e⌝ₛ,S,r) →
    (⌜q⌝ₛ ∈ T ↔ ∃ a b, a ∈ X ∧ b ∈ X ∧
      (∀ p, (p ∈ a ∨ p ∈ b) ↔ ∃ i ∈ ⌜l⌝ₛ, ¬ (i = ⌜e⌝ₛ) ∧
        ⌜Formula.orderedPairMem kpair_convention_l⌝ₚ(i,p,r)) ∧
      ⌜tg_node_m⌝ₚ(⌜k⌝ₛ,S,⌜s⌝ₛ,a,b) ∧ ⌜td_groups_m⌝ₚ(⌜ω⌝ₛ,⌜e⌝ₛ,⌜l⌝ₛ,r,a,b)))⟫
theorem td_node_query0_closed_l : td_node_query0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_node_query0_m,Definitional.Formula.FreeClosed]

def td_node_query_m {d} (ω e n l U D s k q : Term d) : Formula 1 d :=
  td_node_query0_m.bind (fun i => [ω,e,n,l,U,D,s,k,q].get i)

@[simp] theorem td_node_query_m_freeClosed {d} (ω e n l U D s k q : Term d)
    (hω : ω.freeSupport = []) (he : e.freeSupport = []) (hn : n.freeSupport = [])
    (hl : l.freeSupport = []) (hU : U.freeSupport = []) (hD : D.freeSupport = [])
    (hs : s.freeSupport = []) (hk : k.freeSupport = []) (hq : q.freeSupport = []) :
    (td_node_query_m ω e n l U D s k q).FreeClosed := by
  apply (Definitional.Formula.freeClosed_bind_iff_of_closed _ ?_ _).mpr td_node_query0_closed_l
  exact Fin.cases hω (Fin.cases he (Fin.cases hn (Fin.cases hl (Fin.cases hU
    (Fin.cases hD (Fin.cases hs (Fin.cases hk (Fin.cases hq (fun i => Fin.elim0 i)))))))))

/-- 完整语义逐项对应，既不删去分组，也不只检查某一实现。 -/
theorem td_node_query_sat_l (I : kpair_convention_l.Interpretation M) (hKP : M.Models KP)
    {d} (ρ : Env M d) (ω e n l U D s k q : Term d) :
    Formula.satisfies ρ (td_node_query_m ω e n l U D s k q) ↔ Td_node_query_d I
      (ω.eval ρ) (e.eval ρ) (n.eval ρ) (l.eval ρ) (U.eval ρ) (D.eval ρ) (s.eval ρ) (k.eval ρ) (q.eval ρ) := by
  simp only [td_node_query_m,Formula.satisfies_bind,td_node_query0_m,Td_node_query_d,Formula.satisfies_conj_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_forall_iff,Formula.satisfies_imp_iff,Formula.satisfies_iff_iff,
    Formula.satisfies_exists_iff,Formula.satisfies_existsMem_iff,Formula.satisfies_disj_iff,
    Formula.satisfies_neg_iff,Formula.satisfies_extensionalEq_iff_eq hKP.1,
    Formula.satisfies_orderedPairMem_iff I,smem_sat_l I,Formula.satisfies_isTransitive_iff,
    tt_realized_sat_l I hKP,rd_entry0_sat_l hKP.1,tg_node_sat_l I hKP.1,td_groups_sat_l I hKP.1,
    Definitional.Term.eval_weaken]
  rfl

end YesMetaZFC.SetTheory.Internal

/-! ## 同一有限元组的两标签实际追加

每步追加的是原函数图中的配对成员。奇偶仅描述原典范元组；之后的
类型恢复仍允许任意有限排列，不把这里的坐标安排加入子类型条件。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}}
/-- 7.1 的旧回合记录；pending 截点 q 与高度截点 h 严格分开。 -/
structure Td_record_d (J : kpair_convention_l.Interpretation M)
    (ω e k X S a b p α d q h m r : M.Domain) : Prop where
  twice : M.IsOrdinalAddition J d k k
  labels_end : M.SuccessorOf q d
  pending_end : M.SuccessorOf h q
  height_end : M.SuccessorOf m h
  finite : M.mem m ω
  tuple : Fn0_d m X r
  root_before : M.mem e q
  root : Rd_entry_d e S r
  pending : Rd_entry_d q p r
  height : Rd_entry_d h α r
  groups : Td_groups_d J ω e q r a b
  values : ∀ v, (M.mem v a ∨ M.mem v b ∨ v = p) ↔
    ∃ i, M.mem i h ∧ i ≠ e ∧ M.PairMember J i v r

section KP
variable (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP
include hKP

/-- 返回完整图方程，供分组和 pending 坐标同时使用。 -/
theorem td_tuple_append_l {q q' X r p : M.Domain} (oq : M.IsOrdinal q)
    (succ : M.SuccessorOf q' q) (fn : Fn0_d q X r) (hp : M.mem p X) :
    ∃ r', Fn0_d q' X r' ∧
      ∀ i x, Rd_entry_d i x r' ↔ Rd_entry_d i x r ∨ i = q ∧ x = p := by
  have fr := fn0_function_l hKP fn
  obtain ⟨r',seq,graph⟩ := Structure.IsSequenceOfLength.exists_append hKP I
    ⟨oq,fr.1,fr.2.1⟩ (KP.successor_isOrdinal hKP oq succ) succ
  have bound i x (hx : Rd_entry_d i x r') : M.mem x X :=
    ((graph i x).mp hx).elim (fun h => fr.output_mem_of_pairMember h) (fun h => h.2.symm ▸ hp)
  exact ⟨r',fn0_of_function_l hKP
    ⟨seq.2.1,seq.2.2,fun i hi => ((seq.2.2 i).mp hi).imp fun x hx => ⟨bound i x hx,hx⟩⟩,graph⟩

/-- 同一原图在后继长度上的限制，恰多出已选末项的配对码。 -/
theorem td_restrict_next_l {f a a' i j p x : M.Domain}
    (fn : M.IsSetFunction I f) (succ : M.SuccessorOf j i)
    (old : M.IsRestrictionOf I a f i) (next : M.IsRestrictionOf I a' f j)
    (pair : (I).Codes p i x) (hp : M.mem p f) :
    ∀ v, M.mem v a' ↔ M.mem v a ∨ v = p := by
  intro v
  constructor
  · intro hv
    obtain ⟨k,y,code⟩ := next.1 v hv
    obtain ⟨hk,point⟩ := (next.2 k y).mp ⟨v,code,hv⟩
    rcases (succ k).mp hk with hk | eq
    · obtain ⟨u,hu,huA⟩ := (old.2 k y).mpr ⟨hk,point⟩
      exact Or.inl ((I).unique hu code ▸ huA)
    · have eq := hKP.1.eq_of_same_members k i eq
      subst k
      have ey := fn.2 i y x point ⟨p,pair,hp⟩
      subst y
      exact Or.inr ((I).unique code pair)
  · rintro (hv | eq)
    · obtain ⟨k,y,code⟩ := old.1 v hv
      obtain ⟨hk,point⟩ := (old.2 k y).mp ⟨v,code,hv⟩
      obtain ⟨u,hu,huA⟩ := (next.2 k y).mpr ⟨(succ k).mpr (Or.inl hk),point⟩
      exact (I).unique hu code ▸ huA
    · subst v
      obtain ⟨u,hu,huA⟩ := (next.2 i x).mpr ⟨succ.predecessor_mem,⟨p,pair,hp⟩⟩
      exact (I).unique hu pair ▸ huA

/-- 任意已有两标签前缀追加 pending 与高度；逐项保留原前缀，不另作排列。 -/
theorem td_record_append_l {ω e k X S a b p α d q r₀ : M.Domain}
    (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x e) (hq : M.mem q ω)
    (add : M.IsOrdinalAddition I d k k) (sq : M.SuccessorOf q d)
    (fr₀ : Fn0_d q X r₀) (root : Rd_entry_d e S r₀) (groups : Td_groups_d I ω e q r₀ a b)
    (hp : M.mem p X) (hα : M.mem α X) :
    ∃ h m r, Td_record_d I ω e k X S a b p α d q h m r ∧
      ∀ i x, M.mem i q → (Rd_entry_d i x r ↔ Rd_entry_d i x r₀) := by
  obtain ⟨h,sh,hh⟩ := hw.1.2 q hq
  obtain ⟨m,sm,hm⟩ := hw.1.2 h hh
  have oq := hw.members_areOrdinals hKP q hq
  have oh := hw.members_areOrdinals hKP h hh
  obtain ⟨r₁,fr₁,g₁⟩ := td_tuple_append_l hKP oq sh fr₀ hp
  obtain ⟨r,fr,g₂⟩ := td_tuple_append_l hKP oh sm fr₁ hα
  have eqMem := (fr₀.bound_l root).1
  have ne : q ≠ e := fun eq => empty e (eq ▸ eqMem)
  have same i x (hi : M.mem i q) : Rd_entry_d i x r ↔ Rd_entry_d i x r₀ := by
    refine (g₂ i x).trans ⟨?_,fun hx => Or.inl ((g₁ i x).mpr (Or.inl hx))⟩
    · rintro (hx | ⟨eq,_⟩)
      · exact ((g₁ i x).mp hx).elim id
          (fun h => (KP.mem_irrefl_d hKP q (h.1 ▸ hi)).elim)
      · exact (KP.mem_irrefl_d hKP h (eq ▸ (sh i).mpr (Or.inl hi))).elim
  have groups' : Td_groups_d I ω e q r a b := by
    constructor
    · intro v
      exact (groups.1 v).trans ⟨fun ⟨i,hi,ne,par,point⟩ => ⟨i,hi,ne,par,(same i v hi).mpr point⟩,
        fun ⟨i,hi,ne,par,point⟩ => ⟨i,hi,ne,par,(same i v hi).mp point⟩⟩
    · intro v
      exact (groups.2 v).trans ⟨fun ⟨i,hi,ne,par,point⟩ => ⟨i,hi,ne,par,(same i v hi).mpr point⟩,
        fun ⟨i,hi,ne,par,point⟩ => ⟨i,hi,ne,par,(same i v hi).mp point⟩⟩
  have pending : Rd_entry_d q p r := (g₂ q p).mpr (Or.inl ((g₁ q p).mpr (Or.inr ⟨rfl,rfl⟩)))
  refine ⟨h,m,r,?_,same⟩
  refine ⟨add,sq,sh,sm,hm,fr,eqMem,(same e S eqMem).mpr root,pending,
    (g₂ h α).mpr (Or.inr ⟨rfl,rfl⟩),groups',fun v => ⟨?_,?_⟩⟩
  · rintro (ha | hb | eq)
    · obtain ⟨i,hi,ne,point⟩ := (groups'.cover_l v).mp (Or.inl ha)
      exact ⟨i,(sh i).mpr (Or.inl hi),ne,point⟩
    · obtain ⟨i,hi,ne,point⟩ := (groups'.cover_l v).mp (Or.inr hb)
      exact ⟨i,(sh i).mpr (Or.inl hi),ne,point⟩
    · exact ⟨q,sh.predecessor_mem,ne,eq.symm ▸ pending⟩
  · rintro ⟨i,hi,ine,point⟩
    rcases (sh i).mp hi with hi | eq
    · exact ((groups'.cover_l v).mpr ⟨i,hi,ine,point⟩).elim Or.inl (fun h => Or.inr (Or.inl h))
    · have eq := hKP.1.eq_of_same_members i q eq
      subst i
      exact Or.inr (Or.inr ((fn0_function_l hKP fr).1.2 q v p point pending))

private theorem td_selected_append_l {e q q' r r' p a a' : M.Domain} (P : M.Domain → Prop)
    (succ : M.SuccessorOf q' q) (ne : q ≠ e)
    (domain : ∀ i x, Rd_entry_d i x r → M.mem i q)
    (graph : ∀ i x, Rd_entry_d i x r' ↔ Rd_entry_d i x r ∨ i = q ∧ x = p)
    (old : ∀ x, M.mem x a ↔ ∃ i, M.mem i q ∧ i ≠ e ∧ P i ∧ Rd_entry_d i x r)
    (members : ∀ x, M.mem x a' ↔ M.mem x a ∨ P q ∧ x = p) :
    ∀ x, M.mem x a' ↔ ∃ i, M.mem i q' ∧ i ≠ e ∧ P i ∧ Rd_entry_d i x r' := by
  intro x
  refine (members x).trans ⟨?_,?_⟩
  · rintro (hx | ⟨hq,eq⟩)
    · obtain ⟨i,hi,ine,pi,point⟩ := (old x).mp hx
      exact ⟨i,(succ i).mpr (Or.inl hi),ine,pi,(graph i x).mpr (Or.inl point)⟩
    · subst x
      exact ⟨q,succ.predecessor_mem,ne,hq,(graph q p).mpr (Or.inr ⟨rfl,rfl⟩)⟩
  · rintro ⟨i,hi,ine,pi,point⟩
    rcases (succ i).mp hi with hi | eq
    · have oldPoint : Rd_entry_d i x r := ((graph i x).mp point).elim id
        (fun h => (KP.mem_irrefl_d hKP q (h.1 ▸ hi)).elim)
      exact Or.inl ((old x).mpr ⟨i,hi,ine,pi,oldPoint⟩)
    · have eq := hKP.1.eq_of_same_members i q eq
      subst i
      rcases (graph q x).mp point with point | hp
      · exact (KP.mem_irrefl_d hKP q (domain q x point)).elim
      · exact Or.inr ⟨pi,hp.2⟩

end KP
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

/-- 两次真实追加保持奇偶组，且组恰为原图后继限制的成员集合。 -/
theorem Td_groups_d.append_pair_l {ω e q q₁ q₂ X r r₁ r₂ a b a' b' p p' : M.Domain}
    (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x e) (hq : M.mem q ω)
    (sq : M.SuccessorOf q₁ q) (sq₁ : M.SuccessorOf q₂ q₁)
    (fq : Fn0_d q X r) (fq₁ : Fn0_d q₁ X r₁)
    (odd : ¬ Gm_even_d I ω q) (groups : Td_groups_d I ω e q r a b)
    (graph : ∀ i x, Rd_entry_d i x r₁ ↔ Rd_entry_d i x r ∨ i = q ∧ x = p)
    (graph₁ : ∀ i x, Rd_entry_d i x r₂ ↔ Rd_entry_d i x r₁ ∨ i = q₁ ∧ x = p')
    (ma : ∀ x, M.mem x a' ↔ M.mem x a ∨ x = p)
    (mb : ∀ x, M.mem x b' ↔ M.mem x b ∨ x = p') :
    Td_groups_d I ω e q₂ r₂ a' b' := by
  have nq : q ≠ e := fun eq => odd (eq.symm ▸ gm_even_zero_l I hZF hw empty)
  have nq₁ : q₁ ≠ e := fun eq => empty q (eq ▸ sq.predecessor_mem)
  have even := (gm_even_successor_l I hZF hw hq sq).mpr odd
  have first := td_selected_append_l (ZF.modelsKP hZF) (fun i => ¬ Gm_even_d I ω i) sq nq
    (fun i x hx => (fq.bound_l hx).1) graph groups.1
    (fun x => (ma x).trans (by simp only [odd,not_false_eq_true,true_and]))
  have second := td_selected_append_l (ZF.modelsKP hZF) (a' := b) (fun i => Gm_even_d I ω i) sq nq
    (fun i x hx => (fq.bound_l hx).1) graph groups.2
    (fun x => by simp only [odd,false_and,or_false])
  exact ⟨td_selected_append_l (ZF.modelsKP hZF) (a' := a') (fun i => ¬ Gm_even_d I ω i) sq₁ nq₁
      (fun i x hx => (fq₁.bound_l hx).1) graph₁ first
      (fun x => by simp only [even,not_true_eq_false,false_and,or_false]),
    td_selected_append_l (ZF.modelsKP hZF) (fun i => Gm_even_d I ω i) sq₁ nq₁
      (fun i x hx => (fq₁.bound_l hx).1) graph₁ second
      (fun x => (mb x).trans (by simp only [even,true_and]))⟩

end YesMetaZFC.SetTheory.Internal

/-! ## 已恢复元组原位更新为下一 pending 记录

从实际 u 元组截去最后的高度。所有旧变量逐项保留，已选 pending
放入原高度槽，高度移至新末槽。只用 KP 的真实限制和追加，不重新
构造典范标签次序，也不要求关于新类型真值的输入。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel Descriptive
universe u
variable {M : Structure.{u}} (hKP : M.Models KP)
local notation "I" => kp_pair_l hKP

/-- p 是现场提供的实际 pending 对象；完整输出保持原 u 的所有前缀坐标。 -/
theorem td_renew_l {ω e k X S a b p α d q n r : M.Domain}
    (hw : M.IsOmega ω) (empty : ∀ x, ¬ M.mem x e) (hn : M.mem n ω)
    (add : M.IsOrdinalAddition I d k k) (sq : M.SuccessorOf q d) (sn : M.SuccessorOf n q)
    (fn : Fn0_d n X r) (root : Rd_entry_d e S r) (height : Rd_entry_d q α r)
    (groups : Td_groups_d I ω e q r a b) (hp : M.mem p X) :
    ∃ m r', Td_record_d I ω e k X S a b p α d q n m r' ∧
      (∀ i x, M.mem i q → (Rd_entry_d i x r' ↔ Rd_entry_d i x r)) ∧
      (∀ x, Rd_entry_d n x r' ↔ Rd_entry_d q x r) ∧
      (∀ i x, Rd_entry_d i x r' ↔ (M.mem i q ∧ Rd_entry_d i x r) ∨
        (i = q ∧ x = p) ∨ (i = n ∧ x = α)) := by
  have hq := hw.transitive hKP n hn q sn.predecessor_mem
  have oq := hw.members_areOrdinals hKP q hq
  have eqMem := oq.empty_mem_of_nonempty hKP ⟨d,sq.predecessor_mem⟩ empty
  obtain ⟨r₀,data⟩ := res0_exists_l hKP r q X
  have cut := res0_restriction_l hKP fn data
  have fr₀ := fn0_of_function_l hKP (cut.isSetFunctionFromTo (fn0_function_l hKP fn)
    (fun i hi => (sn i).mpr (Or.inl hi)))
  have same i x (hi : M.mem i q) : Rd_entry_d i x r₀ ↔ Rd_entry_d i x r :=
    (cut.2 i x).trans ⟨And.right,fun h => ⟨hi,h⟩⟩
  have groups₀ : Td_groups_d I ω e q r₀ a b := by
    constructor
    · intro x
      exact (groups.1 x).trans ⟨fun ⟨i,hi,ne,par,point⟩ => ⟨i,hi,ne,par,(same i x hi).mpr point⟩,
        fun ⟨i,hi,ne,par,point⟩ => ⟨i,hi,ne,par,(same i x hi).mp point⟩⟩
    · intro x
      exact (groups.2 x).trans ⟨fun ⟨i,hi,ne,par,point⟩ => ⟨i,hi,ne,par,(same i x hi).mpr point⟩,
        fun ⟨i,hi,ne,par,point⟩ => ⟨i,hi,ne,par,(same i x hi).mp point⟩⟩
  obtain ⟨h,m,r',record,kept⟩ := td_record_append_l hKP hw empty hq add sq fr₀
    ((same e S eqMem).mpr root) groups₀ hp (fn.bound_l height).2
  have eh := record.pending_end.eq hKP.1 sn
  subst h
  have old i x (hi : M.mem i q) : Rd_entry_d i x r' ↔ Rd_entry_d i x r :=
    (kept i x hi).trans (same i x hi)
  have oldFn := (fn0_function_l hKP fn).1
  have newFn := (fn0_function_l hKP record.tuple).1
  refine ⟨m,r',record,old,fun x => ⟨?_,?_⟩,fun i x => ⟨?_,?_⟩⟩
  · intro hx
    exact (newFn.2 n x α hx record.height).symm ▸ height
  · intro hx
    exact (oldFn.2 q x α hx height).symm ▸ record.height
  · intro hx
    rcases (record.height_end i).mp (record.tuple.bound_l hx).1 with hi | eq
    · rcases (sn i).mp hi with hi | eq
      · exact Or.inl ⟨hi,(old i x hi).mp hx⟩
      · have eq := hKP.1.eq_of_same_members i q eq
        subst i
        exact Or.inr (Or.inl ⟨rfl,newFn.2 q x p hx record.pending⟩)
    · have eq := hKP.1.eq_of_same_members i n eq
      subst i
      exact Or.inr (Or.inr ⟨rfl,newFn.2 n x α hx record.height⟩)
  · rintro (⟨hi,hx⟩ | ⟨eq,ex⟩ | ⟨eq,ex⟩)
    · exact (old i x hi).mpr hx
    · exact eq.symm ▸ ex.symm ▸ record.pending
    · exact eq.symm ▸ ex.symm ▸ record.height

end YesMetaZFC.SetTheory.Internal

/-! ## 固定 demanding 节点查询的常量域扩张

在大常量池的同一完整类型中，取小池的交类型读取原查询。实际查询码、
实现元组、节点和奇偶两组均保持不变。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (I : kpair_convention_l.Interpretation M) (hKP : M.Models KP)
include hKP

theorem Td_node_query_d.scope_l {ω e n l U D V W s k q : M.Domain}
    (small : Tt_pool_d I ω n U D) (large : Tt_pool_d I ω n V W) (sub : M.MemberSubset U V)
    (query : Td_node_query_d I ω e n l U D s k q) :
    Td_node_query_d I ω e n l V W s k q := by
  refine ⟨small.mono_l I large sub q query.1,fun c X R r δ T S model trans type rS => ?_⟩
  obtain ⟨a,localType,same⟩ := type.constants_restrict_l I hKP small sub
  exact (same q query.1).symm.trans (query.2 c X R r δ a S model trans localType rS)

end YesMetaZFC.SetTheory.Internal
