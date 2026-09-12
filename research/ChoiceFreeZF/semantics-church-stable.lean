import YesMetaZFC.Model.Boolean.Soundness
import YesMetaZFC.SetTheory.Language

/-! # 稳定观察的实际经典语义候选

稳定真值、稳定生成闭包及记录观察给出外延性和配对，并接回原 Hilbert 规则。
并集、分离、幂集等完整 ZF 验证尚未完成；不继承普通观察的原小图忠实嵌入。
-/

namespace ZFStableChurch
universe u v

def SP := {p : Prop // ¬¬p → p}
def dn (p : Prop) : SP := ⟨¬¬p, fun h k => h (fun q => q k)⟩

theorem sp_eq_stable (p q : SP) : ¬¬(p = q) → p = q := by
  intro h
  apply Subtype.ext
  apply propext
  constructor
  · intro hp
    apply q.2
    intro hn
    exact h (fun e => hn (e ▸ hp))
  · intro hq
    apply p.2
    intro hn
    exact h (fun e => hn (e.symm ▸ hq))

structure Fam (X : Type v) where
  I : Type u
  f : I → X

structure Obs where
  X : Type u
  eq_stable : ∀ x y : X, ¬¬(x = y) → x = y
  alg : (X → SP) → X

def C := (o : Obs.{u}) → o.X

theorem c_eq_stable (c d : C.{u}) : ¬¬(c = d) → c = d := by
  intro h
  funext o
  apply o.eq_stable
  intro hn
  exact h (fun e => hn (congrFun e o))

def profile (s : Fam.{u,u+1} C.{u}) (o : Obs.{u}) (x : o.X) : SP :=
  dn (∃ i, s.f i o = x)

def sup (s : Fam.{u,u+1} C.{u}) : C.{u} := fun o => o.alg (profile s o)

/-- 最小稳定闭包；这里只要求已有实际小族，不假设能选出呈现。 -/
def Gen (c : C.{u}) : Prop :=
  ∀ p : C.{u} → SP, (∀ s, (∀ i, (p (s.f i)).1) → (p (sup s)).1) → (p c).1

theorem gen_stable (c : C.{u}) : ¬¬Gen c → Gen c := by
  intro h p hp
  apply (p c).2
  intro hn
  exact h (fun hc => hn (hc p hp))

theorem gen_sup (s : Fam.{u,u+1} C.{u}) (h : ∀ i, Gen (s.f i)) : Gen (sup s) :=
  fun p hp => hp s (fun i => h i p hp)

theorem gen_ind (p : C.{u} → Prop) (hp : ∀ c, ¬¬p c → p c)
    (hs : ∀ s, (∀ i, p (s.f i)) → p (sup s)) {c : C.{u}} (h : Gen c) : p c :=
  h (fun c => ⟨p c, hp c⟩) hs

def V := {c : C.{u} // Gen c}

def v_sup (s : Fam.{u,u+1} V.{u}) : V.{u} :=
  ⟨sup ⟨s.I, fun i => (s.f i).1⟩, gen_sup _ (fun i => (s.f i).2)⟩

def record (o : Obs.{u}) : Obs.{u} where
  X := o.X × (o.X → SP)
  eq_stable x y h := by
    apply Prod.ext
    · apply o.eq_stable; intro hn; exact h (fun e => hn (congrArg Prod.fst e))
    · funext a
      apply sp_eq_stable
      intro hn
      exact h (fun e => hn (congrFun (congrArg Prod.snd e) a))
  alg p :=
    let q (x : o.X) : SP := dn (∃ z, (p z).1 ∧ z.1 = x)
    (o.alg q, q)

theorem record_first (o : Obs.{u}) {c : C.{u}} (h : Gen c) :
    (c (record o)).1 = c o := by
  apply gen_ind (fun c => (c (record o)).1 = c o) (fun c => o.eq_stable _ _) _ h
  intro s ih
  change o.alg (fun x => dn (∃ z, (profile s (record o) z).1 ∧ z.1 = x)) =
    o.alg (profile s o)
  apply congrArg o.alg
  funext x
  apply Subtype.ext
  apply propext
  constructor
  · intro h hn
    apply h
    intro ⟨z, hz, he⟩
    apply hz
    intro ⟨i, hi⟩
    exact hn ⟨i, (ih i).symm.trans ((congrArg Prod.fst hi).trans he)⟩
  · intro h hn
    apply h
    intro ⟨i, hi⟩
    apply hn
    refine ⟨s.f i (record o), ?_, (ih i).trans hi⟩
    exact fun hk => hk ⟨i, rfl⟩

theorem record_second (s : Fam.{u,u+1} C.{u}) (hs : ∀ i, Gen (s.f i)) (o : Obs.{u}) :
    (sup s (record o)).2 = profile s o := by
  funext x
  apply Subtype.ext
  apply propext
  constructor
  · intro h hn
    apply h
    intro ⟨z, hz, he⟩
    apply hz
    intro ⟨i, hi⟩
    exact hn ⟨i, (record_first o (hs i)).symm.trans ((congrArg Prod.fst hi).trans he)⟩
  · intro h hn
    apply h
    intro ⟨i, hi⟩
    apply hn
    refine ⟨s.f i (record o), ?_, (record_first o (hs i)).trans hi⟩
    exact fun hk => hk ⟨i, rfl⟩

theorem gen_shape {c : C.{u}} (h : Gen c) :
    ¬¬∃ s : Fam.{u,u+1} C.{u}, c = sup s ∧ ∀ i, Gen (s.f i) := by
  have h' : Gen c ∧ ¬¬∃ s : Fam.{u,u+1} C.{u}, c = sup s ∧ ∀ i, Gen (s.f i) := by
    apply gen_ind (fun c => Gen c ∧ ¬¬∃ s, c = sup s ∧ ∀ i, Gen (s.f i)) _ _ h
    · intro c hc
      exact ⟨gen_stable c (fun hn => hc (fun hz => hn hz.1)),
        fun hn => hc (fun hz => hz.2 hn)⟩
    · intro s hs
      exact ⟨gen_sup s (fun i => (hs i).1), fun hn => hn ⟨s, rfl, fun i => (hs i).1⟩⟩
  exact h'.2

def Mem (x y : C.{u}) : Prop := ∀ o, ((y (record o)).2 (x o)).1

theorem mem_sup (s : Fam.{u,u+1} C.{u}) (hs : ∀ i, Gen (s.f i)) (x : C.{u}) :
    Mem x (sup s) ↔ ∀ o, (profile s o (x o)).1 := by
  unfold Mem
  simp only [record_second s hs]

/-- 局部成员无需等于呈现中的某个点；外延性只比较全部稳定像。 -/
theorem extensionality (a b : V.{u}) (h : ∀ x : V.{u}, Mem x.1 a.1 ↔ Mem x.1 b.1) : a = b := by
  apply Subtype.ext
  apply c_eq_stable
  intro hn
  apply gen_shape a.2
  intro ⟨s, ha, hs⟩
  apply gen_shape b.2
  intro ⟨t, hb, ht⟩
  apply hn
  rw [ha, hb]
  funext o
  apply congrArg o.alg
  funext x
  apply Subtype.ext
  apply propext
  constructor
  · intro hx hn'
    apply hx
    intro ⟨i, hi⟩
    have ha' : Mem (s.f i) a.1 := by
      rw [ha, mem_sup s hs]
      exact fun o hn => hn ⟨i, rfl⟩
    have hb' := (h ⟨s.f i, hs i⟩).mp ha'
    rw [hb, mem_sup t ht] at hb'
    exact hb' o (fun ⟨j, hj⟩ => hn' ⟨j, hj.trans hi⟩)
  · intro hx hn'
    apply hx
    intro ⟨i, hi⟩
    have hb' : Mem (t.f i) b.1 := by
      rw [hb, mem_sup t ht]
      exact fun o hn => hn ⟨i, rfl⟩
    have ha' := (h ⟨t.f i, ht i⟩).mpr hb'
    rw [ha, mem_sup s hs] at ha'
    exact ha' o (fun ⟨j, hj⟩ => hn' ⟨j, hj.trans hi⟩)

/-- 以下观察和两棵树均为实际实例，排除空观察族导致的退化。 -/
def empty_obs : Obs.{0} where
  X := SP
  eq_stable := sp_eq_stable
  alg p := ⟨¬∃ q, (p q).1, fun h k => h (fun hn => hn k)⟩

def empty : V.{0} := v_sup ⟨PEmpty, PEmpty.elim⟩
def singleton (a : V.{0}) : V.{0} := v_sup ⟨PUnit, fun _ => a⟩

theorem empty_ne_singleton (a : V.{0}) : empty ≠ singleton a := by
  intro e
  have he : (empty.1 empty_obs).1 := fun ⟨_, hq⟩ => hq (fun ⟨i, _⟩ => PEmpty.elim i)
  have hs : ((singleton a).1 empty_obs).1 :=
    Eq.mp (congrArg (fun v : V => (v.1 empty_obs).1) e) he
  exact hs ⟨a.1 empty_obs, fun hn => hn ⟨PUnit.unit, rfl⟩⟩

def pi_obs {I : Type u} (o : I → Obs.{u}) : Obs.{u} where
  X := ∀ i, (o i).X
  eq_stable x y h := by
    funext i
    apply (o i).eq_stable
    intro hn
    exact h (fun e => hn (congrFun e i))
  alg p i := (o i).alg (fun x => dn (∃ z, (p z).1 ∧ z i = x))

theorem pi_eval {I : Type u} (o : I → Obs.{u}) (i : I) {c : C.{u}} (h : Gen c) :
    c (pi_obs o) i = c (o i) := by
  apply gen_ind (fun c => c (pi_obs o) i = c (o i)) (fun c => (o i).eq_stable _ _) _ h
  intro s ih
  change (o i).alg (fun x => dn (∃ z, (profile s (pi_obs o) z).1 ∧ z i = x)) =
    (o i).alg (profile s (o i))
  apply congrArg (o i).alg
  funext x
  apply Subtype.ext
  apply propext
  constructor
  · intro h hn
    apply h
    intro ⟨z, hz, he⟩
    apply hz
    intro ⟨j, hj⟩
    exact hn ⟨j, (ih j).symm.trans ((congrFun hj i).trans he)⟩
  · intro h hn
    apply h
    intro ⟨j, hj⟩
    apply hn
    exact ⟨s.f j (pi_obs o), fun hk => hk ⟨j, rfl⟩, (ih j).trans hj⟩

theorem distinguish (c d : C.{u}) (h : c ≠ d) : ¬¬∃ o, c o ≠ d o := by
  intro hn
  apply h
  funext o
  apply o.eq_stable
  intro he
  exact hn ⟨o, he⟩

def pair (a b : V.{0}) : V.{0} := v_sup ⟨Bool, fun | false => a | true => b⟩

/-- 配对只产生稳定析取；不从观察的局部二选一抽取元层二选一。 -/
theorem pair_mem (x a b : V.{0}) : Mem x.1 (pair a b).1 ↔ ¬¬(x = a ∨ x = b) := by
  let f : Bool → V.{0} := fun | false => a | true => b
  let s : Fam.{0,1} C.{0} := ⟨Bool, fun i => (f i).1⟩
  have hs : ∀ i, Gen (s.f i) := fun i => (f i).2
  change Mem x.1 (sup s) ↔ _
  rw [mem_sup s hs]
  constructor
  · intro hm hn
    have ha : x.1 ≠ a.1 := fun he => hn (Or.inl (Subtype.ext he))
    have hb : x.1 ≠ b.1 := fun he => hn (Or.inr (Subtype.ext he))
    apply distinguish x.1 a.1 ha
    intro ⟨o, ho⟩
    apply distinguish x.1 b.1 hb
    intro ⟨p, hp⟩
    let os : Bool → Obs.{0} := fun | false => o | true => p
    apply hm (pi_obs os)
    intro ⟨i, hi⟩
    cases i with
    | false =>
      apply ho
      exact (pi_eval os false x.2).symm.trans ((congrFun hi false).symm.trans (pi_eval os false a.2))
    | true =>
      apply hp
      exact (pi_eval os true x.2).symm.trans ((congrFun hi true).symm.trans (pi_eval os true b.2))
  · intro h o hn
    apply h
    intro hx
    cases hx with
    | inl hx => exact hn ⟨false, congrArg (fun z : V => z.1 o) hx.symm⟩
    | inr hx => exact hn ⟨true, congrArg (fun z : V => z.1 o) hx.symm⟩

open YesMetaZFC YesMetaZFC.Model YesMetaZFC.Model.Boolean

def algebra : CB_alg SP where
  le p q := p.1 → q.1
  bot := ⟨False, fun h => h id⟩
  le_refl _ := id
  le_trans h k := k ∘ h
  le_antisymm h k := Subtype.ext (propext ⟨h, k⟩)
  bot_le _ := False.elim
  meet p q := ⟨p.1 ∧ q.1, fun h =>
    ⟨p.2 (fun hn => h (fun hpq => hn hpq.1)), q.2 (fun hn => h (fun hpq => hn hpq.2))⟩⟩
  imp p q := ⟨p.1 → q.1, fun h hp => q.2 (fun hn => h (fun f => hn (f hp)))⟩
  le_meet_iff _ _ _ := ⟨fun h => ⟨fun hp => (h hp).1, fun hp => (h hp).2⟩,
    fun ⟨h, k⟩ hp => ⟨h hp, k hp⟩⟩
  le_imp_iff _ _ _ := ⟨fun h ⟨hp, hq⟩ => h hp hq, fun h hp hq => h ⟨hp, hq⟩⟩
  double_neg p := Subtype.ext (propext ⟨p.2, fun h hn => hn h⟩)
  sup p := dn (∃ q, p q ∧ q.1)
  sup_le_iff _ a := ⟨fun h q hq hq' => h (fun hn => hn ⟨q, hq, hq'⟩),
    fun h hp => a.2 (fun hn => hp (fun ⟨q, hq, hq'⟩ => hn (h q hq hq')))⟩

theorem v_eq_stable (a b : V.{0}) : ¬¬(a = b) → a = b := by
  intro h
  apply Subtype.ext
  apply c_eq_stable
  intro hn
  exact h (fun e => hn (congrArg Subtype.val e))

theorem mem_stable (a b : C.{0}) : ¬¬Mem a b → Mem a b := by
  intro h o
  apply ((b (record o)).2 (a o)).2
  intro hn
  exact h (fun hm => hn (hm o))

def structure_model : BV_str.{0,0,0,1,0} SetTheory.PureSetLanguage SP where
  Carrier _ := V.{0}
  nonempty _ := ⟨empty⟩
  funcInterp f := nomatch f
  eqv a b := ⟨a = b, v_eq_stable a b⟩
  relv | .membership, .cons a (.cons b .nil) => ⟨Mem a.1 b.1, mem_stable a.1 b.1⟩

attribute [local implicit_reducible] structure_model algebra SetTheory.signature

theorem structure_laws : BV_laws algebra.toBA_alg structure_model where
  eq_refl _ := Subtype.ext (propext ⟨fun _ => id, fun _ => rfl⟩)
  eq_symm _ _ := Subtype.ext (propext ⟨Eq.symm, Eq.symm⟩)
  eq_trans _ _ _ := fun ⟨h, k⟩ => h.trans k
  fn f := nomatch f
  rel := by
    intro r c xs ys h
    cases r
    cases xs; rename_i a xs; cases xs; rename_i b xs; cases xs
    cases ys; rename_i a' ys; cases ys; rename_i b' ys; cases ys
    constructor
    · intro ⟨hc, hm⟩
      change Mem a'.1 b'.1
      rw [← h.1 hc, ← h.2.1 hc]
      exact hm
    · intro ⟨hc, hm⟩
      change Mem a.1 b.1
      rw [h.1 hc, h.2.1 hc]
      exact hm

theorem structure_rules : Sem_rules (BV_str.model algebra structure_model) :=
  BV_str.rules algebra structure_model structure_laws

#print axioms record_first
#print axioms gen_shape
#print axioms extensionality
#print axioms empty_ne_singleton
#print axioms pair_mem
#print axioms algebra
#print axioms structure_rules
end ZFStableChurch
