import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawEvaluation
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCopySyntax
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawOwnedCopy

/-! # 有界池求值沿原关系复制的保持

先把原函数的共同层像读成实际代表，再读取该支撑的同一个分量。
两个实际函数码的复制给出商类复制，随后直接生成原极限复制的节点公式。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

private theorem Er_eval_d.class_l
    {ω L N T w z Γ Y S k r α E b' f' J O Z A p V W C W' : M.Domain}
    (numbers : Rr_layer_d I ω N T w z)
    (en : Extensional (smdl_structure_l I (R := T) ⟨w, numbers.member⟩))
    (ny : ∃ y, M.mem y Y) (ey : Extensional (smdl_structure_l I (R := S) ny))
    (U u a f m d b ξ ℓ e : (smdl_structure_l I (R := T) ⟨w, numbers.member⟩).Domain)
    (trans : (smdl_structure_l I (R := T) ⟨w, numbers.member⟩).TransitiveSet U)
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (fk : M.IsSetInjectionFromTo I k Γ Y)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s v k)
    (code : Rr_finite_d I ω L N T z α a.val) (fa : Fn0_d m ℓ a) (ds : Ep_space_d ξ m d)
    (ff : Fn0_d d b f) (pair : KPair_d (smdl_structure_l I (R := T) ⟨w, numbers.member⟩) u a f)
    (hbb : Rd_entry_d b.val b' k) (hff : Rd_entry_d f.val f' k)
    (system : Er_graph_d I ω L N T ξ.val ℓ.val e.val z Y S k J O Z A p V W)
    (limit : Di_limit_d A p V W r C W') (value : Er_eval_d I ω L N T z Γ Y k r u.val E) :
    ∃ o n v D i t y U₀ G q C₀ W₀ B x g,
      Er_frame_d I ω L N T ξ.val e.val z Y S k α o n m.val a.val d.val v D i t y U₀ G q C₀ W₀ ∧
      KPair_d M x α B ∧ Rd_entry_d x E r ∧ M.mem B C₀ ∧ M.mem g B ∧
      Rf_fun_d I Y S y f' ∧ Rc_graph_d I Y S t f' g := by
  obtain ⟨_, _, _, _, _, _, _, x₀, B₀, pair₀, _, hxE⟩ := value.read_l hZF numbers en u a f d b code ff pair
  obtain ⟨α₀, B₁, pair₁, o, _, _, hao, _, _⟩ := (system.nodes x₀).mp (limit.projection.bound_l hxE).1
  obtain ⟨eqα, eqB⟩ := kpair_injective_l M pair₁ pair₀
  subst α₀ B₁
  obtain ⟨n, m₀, a₀, d₀, v, D, i, t, y, U₀, G, q, C₀, W₀, frame⟩ := system.components α o hao
  have data := frame
  obtain ⟨hn, fα, hnm, fn, ga, space, _, dc, _, _, rt, hdy, _, _, quotient⟩ := data
  -- 原支撑码确定内部长度和有限幂；代表始终在这个实际分量上读取。
  have eq := (show Rr_finite_d I ω L N T z α a₀ from ⟨n, m₀, hn, fα, hnm, fn, ga⟩).unique_l hZF numbers en code
  subst a₀
  let m₁ : (smdl_structure_l I (R := T) ⟨w, numbers.member⟩).Domain :=
    ⟨m₀, numbers.injection.1.output_mem_of_pairMember hnm⟩
  obtain ⟨_, fm⟩ := (rf_fun_native_l I ⟨w, numbers.member⟩ en m₁ a).mp fn
  have eq : m₀ = m.val := congrArg Subtype.val (fm.domain_eq_l en fa)
  subst m₀
  let d₁ : (smdl_structure_l I (R := T) ⟨w, numbers.member⟩).Domain := ⟨d₀, space.elim fun h _ => h 0⟩
  have actual := (er_space_native_l I ⟨w, numbers.member⟩ en ξ m d₁).mp space
  have eq : d₀ = d.val := congrArg Subtype.val (en.eq_of_same_members d₁ d (fun s => (actual s).trans (ds s).symm))
  subst d₀
  have inside s (hs : M.mem s D) : M.mem s Γ := (carrier s).mpr
    ⟨((dc s).mp hs).1, trans d ((carrier d.val).mp (fk.1.input_mem_of_pairMember hdy)).2
      ⟨s, ((dc s).mp hs).1⟩ ((dc s).mp hs).2⟩
  have ft := fn0_of_function_l (ZF.modelsKP hZF) (rt.isSetFunctionFromTo fk.1 inside)
  obtain ⟨ff', g, graph, x, B, px, hgB, hxE⟩ := value.function_l hZF numbers en ny ey U u a f d b trans
    carrier fk pred code ff pair dc ft rt hdy hbb hff
  obtain ⟨_, table⟩ := system.codes
  have hB := (ep_at_read_l table hao quotient.code.1).mp (system.at_l (limit.projection.bound_l hxE).1 px)
  exact ⟨o, n, v, D, i, t, y, U₀, G, q, C₀, W₀, B, x, g, frame, px, hxE, hB, hgB, ff', graph⟩

/-- 两个有界原函数的实际共同层像对应时，原求值直接满足完整复制的节点公式。 -/
theorem Er_eval_d.copy_node_l
    {ω L N T w z Γ X R k q L' N' T' w' z' Γ' Y S k' q' π σ α α' n E E' b₀ b₁ f₀ f₁
      J O Z A p V W C Q J' O' Z' A' p' V' W' C' Q' : M.Domain}
    (numbers : Rr_layer_d I ω N T w z) (numbers' : Rr_layer_d I ω N' T' w' z')
    (en : Extensional (smdl_structure_l I (R := T) ⟨w, numbers.member⟩))
    (en' : Extensional (smdl_structure_l I (R := T') ⟨w', numbers'.member⟩))
    (nx : ∃ x, M.mem x X) (ny : ∃ y, M.mem y Y)
    (ex : Extensional (smdl_structure_l I (R := R) nx))
    (ey : Extensional (smdl_structure_l I (R := S) ny))
    (U u a f m d b ξ ℓ e : (smdl_structure_l I (R := T) ⟨w, numbers.member⟩).Domain)
    (U' u' a' f' m' d' b' ξ' ℓ' e' : (smdl_structure_l I (R := T') ⟨w', numbers'.member⟩).Domain)
    (trans : (smdl_structure_l I (R := T) ⟨w, numbers.member⟩).TransitiveSet U)
    (trans' : (smdl_structure_l I (R := T') ⟨w', numbers'.member⟩).TransitiveSet U')
    (carrier : ∀ x, M.mem x Γ ↔ M.mem x N ∧ Rd_entry_d x U.val T)
    (carrier' : ∀ x, M.mem x Γ' ↔ M.mem x N' ∧ Rd_entry_d x U'.val T')
    (fk : M.IsSetInjectionFromTo I k Γ X) (fk' : M.IsSetInjectionFromTo I k' Γ' Y)
    (pred : ∀ x y, Rd_entry_d x y k → ∀ v, Rd_entry_d v y R ↔ ∃ s, Rd_entry_d s x T ∧ Rd_entry_d s v k)
    (pred' : ∀ x y, Rd_entry_d x y k' → ∀ v, Rd_entry_d v y S ↔ ∃ s, Rd_entry_d s x T' ∧ Rd_entry_d s v k')
    (code : Rr_finite_d I ω L N T z α a.val) (code' : Rr_finite_d I ω L' N' T' z' α' a'.val)
    (fa : Fn0_d m ℓ a) (fa' : Fn0_d m' ℓ' a') (ds : Ep_space_d ξ m d) (ds' : Ep_space_d ξ' m' d')
    (ff : Fn0_d d b f) (ff' : Fn0_d d' b' f')
    (pair : KPair_d (smdl_structure_l I (R := T) ⟨w, numbers.member⟩) u a f)
    (pair' : KPair_d (smdl_structure_l I (R := T') ⟨w', numbers'.member⟩) u' a' f')
    (hbb : Rd_entry_d b.val b₀ k) (hbb' : Rd_entry_d b'.val b₁ k')
    (hff : Rd_entry_d f.val f₀ k) (hff' : Rd_entry_d f'.val f₁ k') (image : Rd_entry_d f₀ f₁ π)
    (sa : Fn0_d n L α) (sa' : Fn0_d n L' α') (assign : Smap_assign_d I n σ α α')
    (system : Er_graph_d I ω L N T ξ.val ℓ.val e.val z X R k J O Z A p V W)
    (system' : Er_graph_d I ω L' N' T' ξ'.val ℓ'.val e'.val z' Y S k' J' O' Z' A' p' V' W')
    (limit : Di_limit_d A p V W q C Q) (limit' : Di_limit_d A' p' V' W' q' C' Q')
    (value : Er_eval_d I ω L N T z Γ X k q u.val E)
    (value' : Er_eval_d I ω L' N' T' z' Γ' Y k' q' u'.val E') :
    M.mem E C ∧ ∃ x, Rd_entry_d x E q ∧
      Er_node_d I ω L N T ξ.val e.val z X R k L' N' T' ξ'.val e'.val z' Y S k' π σ q' x E' := by
  obtain ⟨o, n₀, v, D, i, t, y, U₀, G, p₀, C₀, W₀, B, x, g, frame, px, hxE, hB, hg, fn, graph⟩ :=
    value.class_l hZF numbers en nx ex U u a f m d b ξ ℓ e trans carrier fk pred code fa ds ff pair hbb hff system limit
  obtain ⟨o', n₁, v', D', i', t', y', U₁, G', p₁, C₁, W₁, B', x', g', frame', px', hxE', hB', hg', _, graph'⟩ :=
    value'.class_l hZF numbers' en' ny ey U' u' a' f' m' d' b' ξ' ℓ' e' trans' carrier' fk' pred'
      code' fa' ds' ff' pair' hbb' hff' system' limit'
  have eq := frame.2.1.domain_eq_l hZF.1 sa
  subst n₀
  have eq := frame'.2.1.domain_eq_l hZF.1 sa'
  subst n₁
  -- 使用给定的函数码图条目，直接构造原商类证书，无需另设复制核。
  have copied : Er_class_d I ω L N T ξ.val e.val z X R k L' N' T' ξ'.val e'.val z' Y S k' π σ α α' B B' :=
    ⟨o, o', n, m.val, a.val, d.val, v, D, i, t, y, U₀, G, p₀, C₀, W₀,
      m'.val, a'.val, d'.val, v', D', i', t', y', U₁, G', p₁, C₁, W₁,
      frame, frame', assign, hB, hB', g, g', hg, hg', f₀, f₁, fn, graph, image, graph'⟩
  exact ⟨(limit.projection.bound_l hxE).2, x, hxE, α, B, α', B', x', px, copied, px', hxE'⟩

end YesMetaZFC.SetTheory.LargeCardinal
