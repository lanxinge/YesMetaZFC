import YesMetaZFC.SetTheory.Descriptive.Tree.RetractionFixed
import YesMetaZFC.Model.SetTheory.Game.NodeEmbedding
import YesMetaZFC.Model.SetTheory.Demand.Reply
import YesMetaZFC.Model.Forcing.Ground.TreeShift

/-! # demanding 树沿历史收缩的实际逆像

实数前缀经同一收缩图变换，两张辅助图保持原样。分离构造逆像树，
完整节点的精确对应由三坐标唯一性证明。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Td_pull_d (ω A F π S T : M.Domain) : Prop := ∀ q, M.mem q T ↔ M.mem q F ∧
  ∃ n s t a b, M.mem n ω ∧ Fn0_d n A s ∧ Rd_entry_d s t π ∧ Tg_node_d I n S t a b ∧ Tg_join_d I n s a b q

def td_pull_node_m {d} (ω A π S q : Term d) : Formula 1 d := set[d] ⟪∃ n s t a b,
  n ∈ ⌜ω⌝ₛ ∧ ⌜fn0_m⌝ₚ(n,⌜A⌝ₛ,s) ∧ ⌜rd_entry0_m⌝ₚ(s,t,⌜π⌝ₛ) ∧
    ⌜tg_node_m⌝ₚ(n,⌜S⌝ₛ,t,a,b) ∧ ⌜tg_join_m⌝ₚ(n,s,a,b,⌜q⌝ₛ)⟫
derive_free_closed td_pull_node_m

theorem td_pull_node_sat_l {d} (ρ : Env M d) (ω A π S q : Term d) :
    Formula.satisfies ρ (td_pull_node_m ω A π S q) ↔
      ∃ n s t a b, M.mem n (ω.eval ρ) ∧ Fn0_d n (A.eval ρ) s ∧ Rd_entry_d s t (π.eval ρ) ∧
        Tg_node_d I n (S.eval ρ) t a b ∧ Tg_join_d I n s a b (q.eval ρ) := by
  simp only [td_pull_node_m,Formula.satisfies_exists_iff,Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff,fn0_sat_l hZF.1,rd_entry0_sat_l hZF.1,tg_node_sat_l I hZF.1,tg_join_sat_l I hZF.1,
    Definitional.Term.eval_weaken]
  rfl

theorem td_pull_exists_l (ω A F π S : M.Domain) : ∃ T, Td_pull_d hZF ω A F π S T := by
  let ρ : Env M 4 := ⟨fun i => [ω,A,π,S].get i,fun _ => ω⟩
  let φ : UnarySchema 4 := { body := td_pull_node_m (.bound 1) (.bound 2) (.bound 3) (.bound 4) .newest }
  obtain ⟨T,read⟩ := ZF.separation_exists_d hZF φ ρ F
  exact ⟨T,fun q => (read q).trans (and_congr_right fun _ => td_pull_node_sat_l hZF ..)⟩

theorem Td_pull_d.node_l {ω A Y F π S T n s a b : M.Domain} (pull : Td_pull_d hZF ω A F π S T)
    (space : Fseq_space_d I ω Y F) {U V P : M.Domain}
    (alphabet : Td_alphabet_d S U V) (pair : M.IsCartesianProduct I P U V) (triple : M.IsCartesianProduct I Y A P)
    (hn : M.mem n ω) : Tg_node_d I n T s a b ↔
      Fn0_d n A s ∧ ∃ t, Rd_entry_d s t π ∧ Tg_node_d I n S t a b := by
  constructor
  · rintro ⟨gs,ga,gb,q,hq,join⟩
    obtain ⟨_,m,s',t,a',b',_,fs',point,node,join'⟩ := (pull q).mp hq
    have eq := join'.1.2.eq hZF.1 join.1.2
    subst m
    have same := join.coordinates_l hZF join' gs ga gb
      ⟨(fn0_function_l (ZF.modelsKP hZF) fs').1,(fn0_function_l (ZF.modelsKP hZF) fs').2.1⟩ node.2.1 node.2.2.1
    obtain ⟨rfl,rfl,rfl⟩ := same
    exact ⟨fs',t,point,node⟩
  · rintro ⟨fs,t,point,node⟩
    have bounds := alphabet.node_l I hZF.1 node
    have fa : Fn0_d n U a := fn0_of_function_l (ZF.modelsKP hZF)
      ⟨node.2.1.1,node.2.1.2,fun i hi => ((node.2.1.2 i).mp hi).imp fun a ha => ⟨bounds.1 i a ha,ha⟩⟩
    have fb : Fn0_d n V b := fn0_of_function_l (ZF.modelsKP hZF)
      ⟨node.2.2.1.1,node.2.2.1.2,fun i hi => ((node.2.2.1.2 i).mp hi).imp fun b hb => ⟨bounds.2 i b hb,hb⟩⟩
    have f := fn0_function_l (ZF.modelsKP hZF) fs
    obtain ⟨_,_,q,_,_,_,join⟩ := tg_join_exists_l I hZF f
      (fn0_function_l (ZF.modelsKP hZF) fa) (fn0_function_l (ZF.modelsKP hZF) fb)
    have fq := join.typed_l hZF fs fa fb pair triple
    exact ⟨⟨f.1,f.2.1⟩,node.2.1,node.2.2.1,q,
      (pull q).mpr ⟨(space q).mpr ⟨n,hn,fn0_function_l (ZF.modelsKP hZF) fq⟩,n,s,t,a,b,hn,fs,point,node,join⟩,join⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 历史逆像关系的有界定义

有限实数图和两张辅助图分别在自己的完整有限空间内量化。
原树节点与新合成节点共用同一辅助图，所以有界公式精确刻画原逆像。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive
universe u
variable {M : Structure.{u}}

-- ω,A,U,V,P,Y,F₀,F₁,F₂,F,π,S,T。
def td_pull_bound_m {d} (v : Fin 13 → Term d) : Formula 1 d := set[d] ⟪
  ⌜v 12⌝ₛ ⊆ ⌜v 9⌝ₛ ∧ (∀ q ∈ ⌜v 9⌝ₛ, q ∈ ⌜v 12⌝ₛ ↔
    (∃ n ∈ ⌜v 0⌝ₛ, ∃ s ∈ ⌜v 6⌝ₛ, ∃ t ∈ ⌜v 6⌝ₛ, ∃ a ∈ ⌜v 7⌝ₛ, ∃ b ∈ ⌜v 8⌝ₛ, ∃ p ∈ ⌜v 11⌝ₛ,
      ⌜rd_entry0_m⌝ₚ(s,t,⌜v 10⌝ₛ) ∧
      ⌜tg_join_bound_m⌝ₚ(n,⌜v 1⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜v 4⌝ₛ,⌜v 5⌝ₛ,t,a,b,p) ∧
      ⌜tg_join_bound_m⌝ₚ(n,⌜v 1⌝ₛ,⌜v 2⌝ₛ,⌜v 3⌝ₛ,⌜v 4⌝ₛ,⌜v 5⌝ₛ,s,a,b,q)))⟫

@[simp] theorem td_pull_bound_closed_l {d} (v : Fin 13 → Term d) (hv : ∀ i, (v i).freeSupport = []) :
    (td_pull_bound_m v).FreeClosed := by
  simp -implicitDefEqProofs [td_pull_bound_m,Definitional.Formula.FreeClosed,hv]

theorem td_pull_bound_delta_l {d} (v : Fin 13 → Term d) : (td_pull_bound_m v).IsDelta0 := by
  unfold td_pull_bound_m
  repeat first
    | exact tg_join_bound_delta_l .. | exact rd_entry0_delta_l ..
    | apply Formula.IsDelta0.conj | apply Formula.IsDelta0.forallMem | apply Formula.IsDelta0.existsMem
    | apply Formula.IsDelta0.iff | exact Formula.IsDelta0.mem .. | exact Formula.IsDelta0.atom _ (by trivial) _

theorem td_pull_bound_sat_l (hZF : M.Models ZF) {d} (ρ : Env M d) (v : Fin 13 → Term d)
    (realSpace : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) (v 0 |>.eval ρ) (v 1 |>.eval ρ) (v 6 |>.eval ρ))
    (leftSpace : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) (v 0 |>.eval ρ) (v 2 |>.eval ρ) (v 7 |>.eval ρ))
    (rightSpace : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) (v 0 |>.eval ρ) (v 3 |>.eval ρ) (v 8 |>.eval ρ))
    (space : Fseq_space_d (kp_pair_l (ZF.modelsKP hZF)) (v 0 |>.eval ρ) (v 5 |>.eval ρ) (v 9 |>.eval ρ))
    (tree : Tree_d (v 9 |>.eval ρ) (v 11 |>.eval ρ))
    (pair : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) (v 4 |>.eval ρ) (v 2 |>.eval ρ) (v 3 |>.eval ρ))
    (triple : M.IsCartesianProduct (kp_pair_l (ZF.modelsKP hZF)) (v 5 |>.eval ρ) (v 1 |>.eval ρ) (v 4 |>.eval ρ)) :
    Formula.satisfies ρ (td_pull_bound_m v) ↔
      Td_pull_d hZF (v 0 |>.eval ρ) (v 1 |>.eval ρ) (v 9 |>.eval ρ) (v 10 |>.eval ρ) (v 11 |>.eval ρ) (v 12 |>.eval ρ) := by
  let I := kp_pair_l (ZF.modelsKP hZF)
  simp only [td_pull_bound_m,Formula.satisfies_conj_iff,Formula.satisfies_subset_iff,
    Formula.satisfies_forallMem_iff,Formula.satisfies_iff_iff,Formula.satisfies_mem_iff,
    Formula.satisfies_existsMem_iff,rd_entry0_sat_l hZF.1,
    tg_join_bound_sat_l hZF,Definitional.Term.eval_weaken,pair,triple]
  constructor
  · rintro ⟨sub,read⟩ q
    constructor
    · intro hq
      obtain ⟨n,hn,s,_,t,_,a,_,b,_,p,hp,st,⟨ft,fa,fb,join⟩,fs,_,_,joined⟩ := (read q (sub q hq)).mp hq
      exact ⟨sub q hq,n,s,t,a,b,hn,fs,st,
        ⟨⟨(fn0_function_l (ZF.modelsKP hZF) ft).1,(fn0_function_l (ZF.modelsKP hZF) ft).2.1⟩,
        ⟨(fn0_function_l (ZF.modelsKP hZF) fa).1,(fn0_function_l (ZF.modelsKP hZF) fa).2.1⟩,
        ⟨(fn0_function_l (ZF.modelsKP hZF) fb).1,(fn0_function_l (ZF.modelsKP hZF) fb).2.1⟩,p,hp,join⟩,joined⟩
    · rintro ⟨hq,n,s,t,a,b,hn,fs,st,node,join⟩
      obtain ⟨ft,fa,fb⟩ := node.typed_l hZF space tree pair triple
      obtain ⟨_,_,_,p,hp,joined⟩ := node
      exact (read q hq).mpr ⟨n,hn,s,(realSpace s).mpr ⟨n,hn,fn0_function_l (ZF.modelsKP hZF) fs⟩,
        t,(realSpace t).mpr ⟨n,hn,fn0_function_l (ZF.modelsKP hZF) ft⟩,
        a,(leftSpace a).mpr ⟨n,hn,fn0_function_l (ZF.modelsKP hZF) fa⟩,
        b,(rightSpace b).mpr ⟨n,hn,fn0_function_l (ZF.modelsKP hZF) fb⟩,p,hp,st,⟨ft,fa,fb,joined⟩,fs,fa,fb,join⟩
  · intro pull
    refine ⟨fun q hq => ((pull q).mp hq).1,?_⟩
    intro q hq
    constructor
    · intro hqT
      obtain ⟨_,n,s,t,a,b,hn,fs,st,node,join⟩ := (pull q).mp hqT
      obtain ⟨ft,fa,fb⟩ := node.typed_l hZF space tree pair triple
      obtain ⟨_,_,_,p,hp,joined⟩ := node
      exact ⟨n,hn,s,(realSpace s).mpr ⟨n,hn,fn0_function_l (ZF.modelsKP hZF) fs⟩,
        t,(realSpace t).mpr ⟨n,hn,fn0_function_l (ZF.modelsKP hZF) ft⟩,
        a,(leftSpace a).mpr ⟨n,hn,fn0_function_l (ZF.modelsKP hZF) fa⟩,
        b,(rightSpace b).mpr ⟨n,hn,fn0_function_l (ZF.modelsKP hZF) fb⟩,p,hp,st,⟨ft,fa,fb,joined⟩,fs,fa,fb,join⟩
    · rintro ⟨n,hn,s,_,t,_,a,_,b,_,p,hp,st,⟨ft,fa,fb,join⟩,fs,_,_,joined⟩
      exact (pull q).mpr ⟨hq,n,s,t,a,b,hn,fs,st,
        ⟨⟨(fn0_function_l (ZF.modelsKP hZF) ft).1,(fn0_function_l (ZF.modelsKP hZF) ft).2.1⟩,
        ⟨(fn0_function_l (ZF.modelsKP hZF) fa).1,(fn0_function_l (ZF.modelsKP hZF) fa).2.1⟩,
        ⟨(fn0_function_l (ZF.modelsKP hZF) fb).1,(fn0_function_l (ZF.modelsKP hZF) fb).2.1⟩,p,hp,join⟩,joined⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 历史逆像进入实际泛型扩张

完整有限空间由地嵌入保持。有界节点等价式因此在扩张中仍然刻画
同一逆像树，包括扩张中新出现的无限对局的全部有限前缀。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
include hi he

theorem Td_pull_d.image_l {ω A U V P Y F₀ F S T π : M.Domain}
    (pull : Td_pull_d hM ω A F π S T)
    (hw : M.IsOmega ω) (hw' : N.IsOmega (e ω))
    (inputs : Fseq_space_d I ω A F₀) (space : Fseq_space_d I ω Y F) (tree : Tree_d F S)
    (pair : M.IsCartesianProduct I P U V) (triple : M.IsCartesianProduct I Y A P) :
    Td_pull_d hN (e ω) (e A) (e F) (e π) (e S) (e T) := by
  obtain ⟨F₁,left⟩ := ZF.fseq_space_exists_l I hM hw U
  obtain ⟨F₂,right⟩ := ZF.fseq_space_exists_l I hM hw V
  let ρ : Env M 13 := ⟨fun i => [ω,A,U,V,P,Y,F₀,F₁,F₂,F,π,S,T].get i,fun _ => ω⟩
  have first := td_pull_bound_sat_l hM ρ Term.bound inputs left right space tree pair triple
  have second := td_pull_bound_sat_l hN (image_env_l e ρ) Term.bound
    (image_fseq_l hM hN e hi he hw hw' inputs)
    (image_fseq_l hM hN e hi he hw hw' left)
    (image_fseq_l hM hN e hi he hw hw' right)
    (image_fseq_l hM hN e hi he hw hw' space) (image_tree_l e hi he tree)
    (image_product_l e hi he pair) (image_product_l e hi he triple)
  exact second.mp ((delta0_image_l e hi he (td_pull_bound_delta_l Term.bound) ρ).mp (first.mpr pull))

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 泛型扩张中的实际最小辅助域

旧节点的每个图条目仍来自旧节点。三坐标配对的单射性逐层识别辅助值，
因此扩张不改变原树实际出现的字母集合。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal Descriptive Model.Forcing.Internal
universe u v
variable {M : Structure.{u}} {N : Structure.{v}}
variable (hM : M.Models ZF) (hN : N.Models ZF) (e : M.Domain → N.Domain)
  (hi : Function.Injective e) (he : ∀ a y, N.mem y (e a) ↔ ∃ c, M.mem c a ∧ e c = y)
local notation "I" => kp_pair_l (ZF.modelsKP hM)
include hi he hN

/-- 节点所在的积字母域可大于实际出现的最小字母域。 -/
theorem Td_alphabet_d.ground_l {ω A U V U₀ V₀ P Y F S : M.Domain}
    (alphabet : Td_alphabet_d S U V) (space : Fseq_space_d I ω Y F) (tree : Tree_d F S)
    (pair : M.IsCartesianProduct I P U₀ V₀) (triple : M.IsCartesianProduct I Y A P) :
    Td_alphabet_d (e S) (e U) (e V) := by
  have letter (side : Bool) (z : N.Domain) : Td_letter_d side (e S) z ↔
      ∃ a, Td_letter_d side S a ∧ e a = z := by
    constructor
    · rintro ⟨q,i,p,x,a,b,t,hq,ip,px,ab,eq⟩
      obtain ⟨q₀,hq₀,rfl⟩ := (he S q).mp hq
      obtain ⟨_,_,fq⟩ := (space q₀).mp (tree.1 q₀ hq₀)
      obtain ⟨i₀,p₀,ip₀,rfl,rfl⟩ := (image_entries_l e he fq.1.1 i p).mp ip
      obtain ⟨x₀,_,t₀,ht₀,px₀⟩ := (triple p₀).mp (fq.output_mem_of_pairMember ip₀)
      obtain ⟨a₀,_,b₀,_,ab₀⟩ := (pair t₀).mp ht₀
      obtain ⟨ex,et⟩ := kpair_injective_l N (image_kpair_l e he px₀) px
      obtain ⟨ea,eb⟩ := kpair_injective_l N (et ▸ image_kpair_l e he ab₀) ab
      refine ⟨if side then b₀ else a₀,⟨q₀,i₀,p₀,x₀,a₀,b₀,t₀,hq₀,ip₀,px₀,ab₀,rfl⟩,?_⟩
      cases side <;> simp only [Bool.false_eq_true,↓reduceIte] at eq ⊢
      · exact ea.trans eq.symm
      · exact eb.trans eq.symm
    · rintro ⟨a,⟨q,i,p,x,b,c,t,hq,ip,px,bc,eq⟩,rfl⟩
      refine ⟨e q,e i,e p,e x,e b,e c,e t,(image_member_l e hi he).mpr hq,
        (image_entry_iff_l e hi he (KP.exists_pair (ZF.modelsKP hM)) hN.1 i p q).mp ip,
        image_kpair_l e he px,image_kpair_l e he bc,?_⟩
      cases side <;> exact congrArg e eq
  constructor
  · intro z; rw [letter false z,he U z]
    exact exists_congr (fun a => and_congr ((alphabet.1 a)) Iff.rfl)
  · intro z; rw [letter true z,he V z]
    exact exists_congr (fun a => and_congr ((alphabet.2 a)) Iff.rfl)

end YesMetaZFC.SetTheory.LargeCardinal
