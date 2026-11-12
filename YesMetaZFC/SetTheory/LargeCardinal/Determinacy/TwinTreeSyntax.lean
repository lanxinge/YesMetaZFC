import YesMetaZFC.SetTheory.LargeCardinal.Game.Corollary610
import YesMetaZFC.SetTheory.LargeCardinal.Cardinals.TreeProjectionTransfer
import YesMetaZFC.SetTheory.Descriptive.Game.ClosedDeterminacy
import YesMetaZFC.Model.Forcing.Collapse.ProductRankAbsorption
import YesMetaZFC.Model.Forcing.Collapse.ProductQueryTop
import YesMetaZFC.Model.Forcing.Order.QueryContext
import YesMetaZFC.Model.Forcing.Reflection.Criterion

/-! # 同一坍缩扩张中的双树二择一

6.10 与 6.7 的两个泛型分支必须在同一个名称扩张中对弈。规范名称求值的
唯一性识别两次构造的地嵌入，实际对局同时避开两树，与穷尽相矛盾。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

def Td_cover_d (I : kpair_convention_l.Interpretation M) (ω A Y F T Z G S : M.Domain) : Prop :=
  ∀ x, M.IsSetFunctionFromTo I x ω A → Tp_projection_d I ω A Y F T x ∨ Tp_projection_d I ω A Z G S x

def td_cover_m {d} (ω A Y F T Z G S : Term d) : Formula 1 d := set[d] ⟪∀ x,
  ⌜Formula.isFunctionFromTo kpair_convention_l⌝ₚ(x,⌜ω⌝ₛ,⌜A⌝ₛ) →
  ⌜tp_projection_m⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜Y⌝ₛ,⌜F⌝ₛ,⌜T⌝ₛ,x) ∨
  ⌜tp_projection_m⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜Z⌝ₛ,⌜G⌝ₛ,⌜S⌝ₛ,x)⟫
derive_free_closed td_cover_m

theorem td_cover_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {d}
    (ρ : Env M d) (ω A Y F T Z G S : Term d) : Formula.satisfies ρ (td_cover_m ω A Y F T Z G S) ↔
    Td_cover_d I (ω.eval ρ) (A.eval ρ) (Y.eval ρ) (F.eval ρ) (T.eval ρ) (Z.eval ρ) (G.eval ρ) (S.eval ρ) := by
  simp only [td_cover_m, Td_cover_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_isFunctionFromTo_iff I hE, Formula.satisfies_disj_iff,
    tp_projection_sat_l I hE, Definitional.Term.eval_weaken]; rfl

section Battle
variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem td_battle_l {ω A Y F T Z G S : M.Domain} (hw : M.IsOmega ω)
    (cover : Td_cover_d I ω A Y F T Z G S)
    (left : Tp_win_d hZF false true ω A Y F T) (right : Tp_win_d hZF true false ω A Z G S) : False := by
  obtain ⟨H, J, B, W, τ, hist, runs, turns, payoff, win⟩ := left
  obtain ⟨H', J', B', W', σ, hist', runs', turns', payoff', win'⟩ := right
  have eqH : H' = H := hZF.1.eq_of_same_members H' H fun s => (hist' s).trans (hist s).symm
  have eqJ : J' = J := hZF.1.eq_of_same_members J' J fun n => (turns' n).trans (turns n).symm
  subst H' J'
  obtain ⟨x, fx, follows, follows'⟩ := cg_battle_l hZF hw hist win'.1 win.1
  have noT : ¬ Tp_projection_d I ω A Y F T x :=
    fun p => win.2 x ((runs x).mpr fx) follows' ((payoff x).mpr ⟨(runs x).mpr fx, p⟩)
  have noS := ((payoff' x).mp (win'.2 x ((runs' x).mpr fx) follows)).2
  exact (cover x fx).elim noT noS

end Battle
variable (hZFC : M.Models ZFC)
local notation "hM" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hM)

theorem td_generic_dichotomy_l {ω δ A X a Γ Y F T Λ Z G S C Q : M.Domain}
    (hw : M.IsOmega ω) (hd : Woodin_d I δ) (rank : V_d I δ X) (hA : M.mem A X) (ha : M.mem a A)
    (pair : M.IsCartesianProduct I Y A Γ) (space : Fseq_space_d I ω Y F) (tree : Tree_d F T)
    (pair' : M.IsCartesianProduct I Z A Λ) (space' : Fseq_space_d I ω Z G) (tree' : Tree_d G S)
    (collapse : Fseq_space_d I ω δ C)
    (order : ∀ p q, Entry_d M p q Q ↔ M.mem p C ∧ M.mem q C ∧ M.MemberSubset q p)
    (O : Cond_order_d M C Q C) {U : M.Domain → Prop} (generic : Generic_d M C Q C U)
    {p : M.Domain} (hp : U p)
    (e : M.Domain → (extension_l M hM C Q C U).Domain)
    (hi : Function.Injective e)
    (he : ∀ a y, (extension_l M hM C Q C U).mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
    (hv : ∀ a t, Check_d M p a t → Qval_d M C Q C U t (e a))
    (cover : Td_cover_d (kp_pair_l (ZF.modelsKP (preserves_zf_l O hM generic)))
      (e ω) (e A) (e Y) (e F) (e T) (e Z) (e G) (e S)) :
    Td_cover_d I ω A Y F T Z G S ∧
      (Tp_win_d hM true true ω A Y F T ∨ Tp_win_d hM false false ω A Z G S) := by
  let N := extension_l M hM C Q C U
  have hN : N.Models ZF := preserves_zf_l O hM generic
  have hwN := image_omega_l (hEN := hN.1) e hi he hM (internal_foundation_l O hM generic) hw
    (fun D => KP.difference_exists_d (ZF.modelsKP hN) D (e ω))
  refine ⟨fun x fx => ?_, ?_⟩
  · have fxN := image_function_l (hEN := hN.1) (hPN := KP.exists_pair (ZF.modelsKP hN)) e hi he fx
    exact (cover (e x) fxN).imp
      (tp_projection_reflect_l hM hN e hi he hw hwN (ZFC.dc_l I hZFC hw) pair space tree fx)
      (tp_projection_reflect_l hM hN e hi he hw hwN (ZFC.dc_l I hZFC hw) pair' space' tree' fx)
  · rcases tg_corollary610_l hZFC hw hd rank hA ha pair space tree with win | win
    · exact Or.inl win
    rcases tg_corollary67_l hZFC hw hd rank hA ha pair' space' tree' with win' | win'
    · exact Or.inr win'
    have identify (f : M.Domain → N.Domain)
        (values : ∀ a t, Check_d M p a t → Qval_d M C Q C U t (f a)) : f = e := by
      funext a
      obtain ⟨t, ht, _⟩ := zf_check_l M hM (generic.proper p hp).1 a
      exact qval_unique_l (values a t ht) (hv a t ht)
    obtain ⟨f, _, _, fv, left⟩ := win C Q collapse order O U generic p hp
    obtain ⟨g, _, _, gv, right⟩ := win' C Q collapse order O U generic p hp
    have ef := identify f fv
    have eg := identify g gv
    subst f g
    exact (td_battle_l hN hwN cover left right).elim

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 同一次小坍缩扩张中的原正负树穷尽

原小泛型先被实际吸收到主乘积。原秩模型的名字覆盖把每个小实数送入
原 R*，统一最小代码的顶条件判定再产生一侧原正负条件。对应原树在大
扩张中的分支由完整构枝给出；小扩张中的截面秩反射最后收回该投影。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel InnerModel.Relative Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
variable {c X R : M.Domain}
  (source : Smem_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c X R) (trans : M.TransitiveSet X)
  (ω : (smdl_structure_l (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) (R := R) source.1.2.1).Domain)
  (hw : M.IsOmega ω.val) (certificate : Zc_model_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω.val c X R)
include trans

theorem qs_collapse_cover_l {φ : Formula 1 4} (hc : φ.FreeClosed) {θ : M.Domain} (rank : V_d I θ X)
    {A₀ P V W₀ σ a₀ o κ q₀ sa sq : (smdl_structure_l I (R := R) source.1.2.1).Domain}
    (fa : (smdl_structure_l I (R := R) source.1.2.1).IsSetFunctionFromTo
      (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l (certificate.native_l I hZF hw)))) A₀ ω W₀)
    (product : Fp_product_d (ZFC.models_zf_l (certificate.native_l I hZF hw)) ω A₀ P V)
    (name : Rp_name_d (ZFC.models_zf_l (certificate.native_l I hZF hw)) ω A₀ P σ)
    (binary : Bc_binary_d ω a₀) (empty : ∀ x, ¬ (smdl_structure_l I (R := R) source.1.2.1).mem x o)
    (alphabet : Entry_d (smdl_structure_l I (R := R) source.1.2.1) o κ A₀) (hκ : M.IsUncountableCardinal I ω.val κ.val)
    (ca : Check_d (smdl_structure_l I (R := R) source.1.2.1) o a₀ sa)
    (cq : Check_d (smdl_structure_l I (R := R) source.1.2.1) o q₀ sq)
    (minimum : Forces_d (smdl_structure_l I (R := R) source.1.2.1) P V P (dm_min_m φ)
      (⟨fun i => [σ,sa,sq].get i,fun _ => σ⟩ : Env (smdl_structure_l I (R := R) source.1.2.1) 3) o)
    {u S L T E K Wₛ D J Ys ds hs Fs As Zg Yg dg hg lg rg Fg Ag C Z W Y a b c' d' l r F A
      de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An positive negative : M.Domain}
    (sh : Sh_tree_d hZF ω.val c X R u S L T E K Wₛ D J Ys ds hs Fs As)
    (gn : Gn_tree_d hZF ω.val X P.val V.val Zg Yg dg hg lg rg Fg Ag)
    (joint : Jt_tree_d hZF ω.val X P.val C Ys Yg Zg Fs As Fg Ag ds dg hg lg Z W Y a b c' d' l r F A)
    (link : Nr_link_d hZF joint V.val de df Zn Wn Hn an bn cn dn ln rn Yn dx dh Fn An)
    (pos : Qs_tree_d hZF φ true link.tree σ.val a₀.val positive)
    (neg : Qs_tree_d hZF φ false link.tree σ.val a₀.val negative)
    (params : Jt_params_d ω.val X P.val V.val C)
    {α Q U : M.Domain} (collapse : Fseq_space_d I ω.val α Q) (bound : M.MemberSubset α κ.val)
    (O : Cond_order_d M Q U Q)
    (order : ∀ p q, Entry_d M p q U ↔ M.mem p Q ∧ M.mem q Q ∧ M.MemberSubset q p)
    (s : Nat → M.Domain) (onto : Function.Surjective s) {H : M.Domain → Prop}
    (small : Generic_d M Q U Q H) :
    ∃ k : M.Domain → (extension_l M hZF Q U Q H).Domain,
      (∀ a, Gval_d M Q U Q H a (k a)) ∧
      Td_cover_d (kp_pair_l (ZF.modelsKP (preserves_zf_l O hZF small)))
        (k ω.val) (k ω.val) (k Yn) (k Fn) (k positive) (k Yn) (k Fn) (k negative) := by
  let N := smdl_structure_l I (R := R) source.1.2.1
  have native := ZFC.models_zf_l (certificate.native_l I hZF hw)
  have ni : Function.Injective (Subtype.val : (N).Domain → M.Domain) := fun _ _ eq => Subtype.ext eq
  have nf := smem_full_l I source trans
  -- 原内部 ω 由其规范像的唯一性识别，不增加源自然数标准性的假设。
  have hwN : (N).IsOmega ω := by
    obtain ⟨w,hwn⟩ := ZF.exists_omega native
    have moved : M.IsOmega w.val := image_omega_l (hEN := hZF.1) Subtype.val ni nf native
      (fun _ => KP.mem_minimal_exists_d (ZF.modelsKP hZF)) hwn
      (fun D => KP.difference_exists_d (ZF.modelsKP hZF) D w.val)
    have eq : w = ω := ni (hZF.1.eq_of_same_members w.val ω.val
      (fun z => ⟨moved.2 ω.val hw.1 z,hw.2 w.val moved.1 z⟩))
    exact eq ▸ hwn
  obtain ⟨G,g,ι,ii,ifull,over,j,ground,capture⟩ := Smem_d.countable_absorb_names_l hZFC source trans rank native
    hwN fa product empty alphabet hκ collapse bound O order s onto small
  have O' := image_cond_order_l (ZF.modelsKP native) hZF.1 Subtype.val ni nf (product.order_l native)
  have gN := g.ground_pull_l (ZF.modelsKP native) hZF.1 Subtype.val ni nf
  let B := extension_l M hZF P.val V.val P.val G
  let C₀ := extension_l M hZF Q U Q H
  have hB := preserves_zf_l O' hZF g
  have hCZFC := preserves_zfc_l O hZFC small
  have hC := ZFC.models_zf_l hCZFC
  obtain ⟨b₁,hb₁⟩ := g.inhabited
  obtain ⟨j₀,jc,jf,ji⟩ := check_map_l O' hZF g hb₁
  have eqj : j₀ = j := funext fun a => (gval_check_map_l O' hZF g hb₁ j₀ jc a (j a)).mp (ground a)
  subst j₀
  obtain ⟨b₂,hb₂⟩ := small.inhabited
  obtain ⟨k,kc,kf,ki⟩ := check_map_l O hZF small hb₂
  have base a := (gval_check_map_l O hZF small hb₂ k kc a (k a)).mpr rfl
  have commute a : ι (k a) = j a := (over a (k a) (base a)).unique_l O' hZF g (ground a)
  have hwC : C₀.IsOmega (k ω.val) := image_omega_l (hEN := hC.1) k ki kf hZF
    (internal_foundation_l O hZF small) hw (fun D => KP.difference_exists_d (ZF.modelsKP hC) D (k ω.val))
  have hwB : B.IsOmega (j ω.val) := image_omega_l (hEN := hB.1) j ji jf hZF
    (internal_foundation_l O' hZF g) hw (fun D => KP.difference_exists_d (ZF.modelsKP hB) D (j ω.val))
  have hwι : B.IsOmega (ι (k ω.val)) := (commute ω.val).symm ▸ hwB
  have letters := image_product_l (hEN := hC.1) (hPN := KP.exists_pair (ZF.modelsKP hC)) k ki kf link.tree.letters.product
  have space := image_fseq_l hZF hC k ki kf hw hwC link.tree.sequences
  refine ⟨k,base,fun x fx => ?_⟩
  have real := fn0_of_function_l (ZF.modelsKP hC) fx
  obtain ⟨_,τ,named,old⟩ := capture (k ω.val) (base ω.val) x real
  have named₀ := named
  obtain ⟨_,y,value,_,_,_⟩ := named₀
  obtain ⟨go,side⟩ := name.query_top_l native hc hwN fa product binary empty ca cq minimum gN value (old y value)
  have target : Fn0_d (j ω.val) (j ω.val) (ι x) := by
    have moved := fn0_of_function_l (ZF.modelsKP hB) (image_function_l ι ii ifull fx)
    simpa only [commute] using moved
  -- 原树的像中实际构枝，然后以小扩张自己的截面秩排除新增旧实数投影。
  have reflect (sign : Bool) (Aq : M.Domain) (tree : Qs_tree_d hZF φ sign link.tree σ.val a₀.val Aq)
      (p : (N).Domain) (hp : G p.val) (force : Qs_force_d φ sign P V σ ω a₀ τ o p) :
      Tp_projection_d (kp_pair_l (ZF.modelsKP hC)) (k ω.val) (k ω.val) (k Yn) (k Fn) (k Aq) x := by
    obtain ⟨z,fz,branch,projection⟩ := tree.extension_complete_l hZFC hc source trans ω P V σ a₀ p o τ hw certificate
      (product.order_l native) g j ji jf ground sh gn joint link params hp go target named name.name force
    have project : Tp_projection_d (kp_pair_l (ZF.modelsKP hB)) (j ω.val) (j ω.val) (j Yn) (j Fn) (j Aq) (ι x) :=
      ⟨z,fn0_function_l (ZF.modelsKP hB) fz,branch,fn0_function_l (ZF.modelsKP hB) target,projection⟩
    have project' : Tp_projection_d (kp_pair_l (ZF.modelsKP hB)) (ι (k ω.val)) (ι (k ω.val))
        (ι (k Yn)) (ι (k Fn)) (ι (k Aq)) (ι x) := by simpa only [commute] using project
    exact tp_projection_reflect_l hC hB ι ii ifull hwC hwι (ZFC.dc_l (kp_pair_l (ZF.modelsKP hC)) hCZFC hwC)
      letters space (image_tree_l k ki kf tree.tree) fx project'
  rcases side with ⟨p,hp,force⟩ | ⟨p,hp,force⟩
  · exact Or.inl (reflect true positive pos p hp force)
  · exact Or.inr (reflect false negative neg p hp force)

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 双树论证的原一阶公式

只编码原数学前提、规范名称和原内部力迫关系，供带参数可数反射使用。
反射返回的是原地模型中的实际获胜策略存在性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u
variable {M : Structure.{u}}

def tp_win_m (b positive : Bool) {d} (ω A Y F T : Term d) : Formula 1 d :=
  let payoff {d} (ω A Y F T x : Term d) :=
    if positive then tp_projection_m ω A Y F T x else .neg (tp_projection_m ω A Y F T x)
  set[d] ⟪∃ H J B W σ,
    ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,H) ∧
    ⌜Formula.isFunctionSpace kpair_convention_l⌝ₚ(B,⌜ω⌝ₛ,⌜A⌝ₛ) ∧
    (∀ n, n ∈ J ↔ n ∈ ⌜ω⌝ₛ ∧ ⌜gm_even_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,n)) ∧
    (∀ x, x ∈ W ↔ x ∈ B ∧ ⌜payoff⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,⌜Y⌝ₛ,⌜F⌝ₛ,⌜T⌝ₛ,x)) ∧
    ⌜cg_win_m b⌝ₚ(⌜ω⌝ₛ,⌜A⌝ₛ,H,J,B,W,σ)⟫

@[simp] theorem tp_win_closed_l (b positive : Bool) {d} (ω A Y F T : Term d)
    (hw : ω.freeSupport = []) (ha : A.freeSupport = []) (hy : Y.freeSupport = [])
    (hf : F.freeSupport = []) (ht : T.freeSupport = []) : (tp_win_m b positive ω A Y F T).FreeClosed := by
  cases positive <;> simp -implicitDefEqProofs [tp_win_m, Definitional.Formula.FreeClosed, hw, ha, hy, hf, ht]

theorem tp_win_sat_l (hZF : M.Models ZF) (b positive : Bool) {d} (ρ : Env M d) (ω A Y F T : Term d) :
    Formula.satisfies ρ (tp_win_m b positive ω A Y F T) ↔
    Tp_win_d hZF b positive (ω.eval ρ) (A.eval ρ) (Y.eval ρ) (F.eval ρ) (T.eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  cases positive <;> simp only [tp_win_m, Tp_win_d, Bool.false_eq_true, ↓reduceIte,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, fseq_space_sat_l I hZF.1,
    Formula.satisfies_isFunctionSpace_iff I hZF.1, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_mem_iff, gm_even_sat_l I hZF.1,
    tp_projection_sat_l I hZF.1, Formula.satisfies_neg_iff, cg_win_sat_l I hZF.1,
    Definitional.Term.eval_weaken] <;> rfl

def td_cover0_m : Formula 1 8 :=
  td_cover_m (.bound 0) (.bound 1) (.bound 2) (.bound 3) (.bound 4) (.bound 5) (.bound 6) (.bound 7)

theorem td_cover0_closed_l : td_cover0_m.FreeClosed := by
  simp -implicitDefEqProofs [td_cover0_m]

def td_checks_m {d} (p : Term d) (a t : Fin 8 → Term d) : Formula 1 d :=
  .conj (check_m p (a 0) (t 0)) (.conj (check_m p (a 1) (t 1))
  (.conj (check_m p (a 2) (t 2)) (.conj (check_m p (a 3) (t 3))
  (.conj (check_m p (a 4) (t 4)) (.conj (check_m p (a 5) (t 5))
  (.conj (check_m p (a 6) (t 6)) (check_m p (a 7) (t 7))))))))

@[simp] theorem td_checks_closed_l {d} (p : Term d) (a t : Fin 8 → Term d)
    (hp : p.freeSupport = []) (ha : ∀ i, (a i).freeSupport = []) (ht : ∀ i, (t i).freeSupport = []) :
    (td_checks_m p a t).FreeClosed := by
  simp -implicitDefEqProofs [td_checks_m, Definitional.Formula.FreeClosed, hp, ha, ht]

theorem td_checks_sat_l (hE : Extensional M) {d} (ρ : Env M d) (p : Term d) (a t : Fin 8 → Term d) :
    Formula.satisfies ρ (td_checks_m p a t) ↔ ∀ i, Check_d M (p.eval ρ) ((a i).eval ρ) ((t i).eval ρ) := by
  simp only [td_checks_m, Formula.satisfies_conj_iff, check_sat_l M hE]
  exact ⟨fun ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ => Fin.cases h0 (Fin.cases h1 (Fin.cases h2
    (Fin.cases h3 (Fin.cases h4 (Fin.cases h5 (Fin.cases h6 (fun i => by
      have eq : i = 0 := Fin.ext (by omega); exact eq ▸ h7))))))),
    fun h => ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7⟩⟩

def td_order_m {d} (C Q : Term d) : Formula 1 d := set[d] ⟪∀ p q,
  ⌜entry_m⌝ₚ(p,q,⌜Q⌝ₛ) ↔ p ∈ ⌜C⌝ₛ ∧ q ∈ ⌜C⌝ₛ ∧ q ⊆ p⟫
derive_free_closed td_order_m

theorem td_order_sat_l (hE : Extensional M) {d} (ρ : Env M d) (C Q : Term d) :
    Formula.satisfies ρ (td_order_m C Q) ↔
    ∀ p q, Entry_d M p q (Q.eval ρ) ↔ M.mem p (C.eval ρ) ∧ M.mem q (C.eval ρ) ∧ M.MemberSubset q p := by
  simp only [td_order_m, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, entry_sat_l M hE, Formula.satisfies_mem_iff,
    Formula.satisfies_subset_iff, Definitional.Term.eval_weaken]; rfl

def td_parameters_m : Fin 8 → Term 24 := fun i =>
  [(.bound 0 : Term 24), .bound 2, .bound 6, .bound 7, .bound 8, .bound 10, .bound 11, .bound 12].get i

def td_names_m : Fin 8 → Term 24 := fun i => .bound ⟨i.val + 16, by omega⟩

def td_input_m : Formula 1 24 :=
  let ω := Term.bound 0; let δ := Term.bound 1; let A := Term.bound 2; let X := Term.bound 3
  let a := Term.bound 4; let Γ := Term.bound 5; let Y := Term.bound 6; let F := Term.bound 7
  let T := Term.bound 8; let Λ := Term.bound 9; let Z := Term.bound 10; let G := Term.bound 11
  let S := Term.bound 12; let C := Term.bound 13; let Q := Term.bound 14; let p := Term.bound 15
  .conj (set[24] ⟪⌜Formula.isOmega⌝ₚ(⌜ω⌝ₛ) ∧ ⌜woodin_m (𝒞 := kpair_convention_l)⌝ₚ(⌜δ⌝ₛ) ∧
    ⌜v_m kpair_convention_l⌝ₚ(⌜δ⌝ₛ,⌜X⌝ₛ) ∧ ⌜A⌝ₛ ∈ ⌜X⌝ₛ ∧ ⌜a⌝ₛ ∈ ⌜A⌝ₛ ∧
    ⌜Formula.isCartesianProduct kpair_convention_l⌝ₚ(⌜Y⌝ₛ,⌜A⌝ₛ,⌜Γ⌝ₛ) ∧
    ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜Y⌝ₛ,⌜F⌝ₛ) ∧ ⌜tree_m⌝ₚ(⌜F⌝ₛ,⌜T⌝ₛ) ∧
    ⌜Formula.isCartesianProduct kpair_convention_l⌝ₚ(⌜Z⌝ₛ,⌜A⌝ₛ,⌜Λ⌝ₛ) ∧
    ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜Z⌝ₛ,⌜G⌝ₛ) ∧ ⌜tree_m⌝ₚ(⌜G⌝ₛ,⌜S⌝ₛ) ∧
    ⌜fseq_space_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ,⌜δ⌝ₛ,⌜C⌝ₛ) ∧ ⌜td_order_m⌝ₚ(⌜C⌝ₛ,⌜Q⌝ₛ)⟫)
    (.conj (td_checks_m p td_parameters_m td_names_m) (force_at_m td_cover0_m td_names_m C Q C p))

theorem td_input_closed_l : td_input_m.FreeClosed := by
  have hp : ∀ i, (td_parameters_m i).freeSupport = [] := by simp [td_parameters_m, Fin.forall_fin_succ]
  have hn : ∀ i, (td_names_m i).freeSupport = [] := fun _ => rfl
  simp -implicitDefEqProofs [td_input_m, Definitional.Formula.FreeClosed, hp, hn, td_cover0_closed_l]

def Td_input_d (hZF : M.Models ZF) (ρ : Env M 24) : Prop :=
  let I := kp_pair_l (ZF.modelsKP hZF); let a := ρ.bound
  (M.IsOmega (a 0) ∧ Woodin_d I (a 1) ∧ V_d I (a 1) (a 3) ∧ M.mem (a 2) (a 3) ∧ M.mem (a 4) (a 2) ∧
    M.IsCartesianProduct I (a 6) (a 2) (a 5) ∧ Fseq_space_d I (a 0) (a 6) (a 7) ∧ Tree_d (a 7) (a 8) ∧
    M.IsCartesianProduct I (a 10) (a 2) (a 9) ∧ Fseq_space_d I (a 0) (a 10) (a 11) ∧ Tree_d (a 11) (a 12) ∧
    Fseq_space_d I (a 0) (a 1) (a 13) ∧
    ∀ p q, Entry_d M p q (a 14) ↔ M.mem p (a 13) ∧ M.mem q (a 13) ∧ M.MemberSubset q p) ∧
  (∀ i, Check_d M (a 15) ((td_parameters_m i).eval ρ) ((td_names_m i).eval ρ)) ∧
  Forces_d M (a 13) (a 14) (a 13) td_cover0_m ⟨fun i => (td_names_m i).eval ρ, ρ.free⟩ (a 15)

theorem td_input_sat_l (hZF : M.Models ZF) (ρ : Env M 24) :
    Formula.satisfies ρ td_input_m ↔ Td_input_d hZF ρ := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [td_input_m, Td_input_d, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff,
    woodin_sat_l I hZF.1, v_sat_l I hZF.1, Formula.satisfies_mem_iff,
    Formula.satisfies_isCartesianProduct_iff I, fseq_space_sat_l I hZF.1, tree_sat_l,
    td_order_sat_l hZF.1, td_checks_sat_l hZF.1, force_at_sat_l]; rfl

def td_output_m : Formula 1 24 := .conj
  (td_cover_m (.bound 0) (.bound 2) (.bound 6) (.bound 7) (.bound 8) (.bound 10) (.bound 11) (.bound 12))
  (.disj (tp_win_m true true (.bound 0) (.bound 2) (.bound 6) (.bound 7) (.bound 8))
    (tp_win_m false false (.bound 0) (.bound 2) (.bound 10) (.bound 11) (.bound 12)))

theorem td_output_closed_l : td_output_m.FreeClosed := by
  simp -implicitDefEqProofs [td_output_m, Definitional.Formula.FreeClosed]

theorem td_output_sat_l (hZF : M.Models ZF) (ρ : Env M 24) :
    Formula.satisfies ρ td_output_m ↔
    Td_cover_d (kp_pair_l (ZF.modelsKP hZF)) (ρ.bound 0) (ρ.bound 2) (ρ.bound 6) (ρ.bound 7)
      (ρ.bound 8) (ρ.bound 10) (ρ.bound 11) (ρ.bound 12) ∧
    (Tp_win_d hZF true true (ρ.bound 0) (ρ.bound 2) (ρ.bound 6) (ρ.bound 7) (ρ.bound 8) ∨
      Tp_win_d hZF false false (ρ.bound 0) (ρ.bound 2) (ρ.bound 10) (ρ.bound 11) (ρ.bound 12)) := by
  simp only [td_output_m, Formula.satisfies_conj_iff, Formula.satisfies_disj_iff,
    td_cover_sat_l (kp_pair_l (ZF.modelsKP hZF)) hZF.1, tp_win_sat_l hZF]; rfl

end YesMetaZFC.SetTheory.LargeCardinal
