# (De-)Serializing Garble Values

If the optional `"serde"` crate feature is enabled, Garble supports serializing literal values to/from formats supported via [serde](https://serde.rs/). The following [ABNF](https://en.wikipedia.org/wiki/Augmented_Backus%E2%80%93Naur_form) grammar shows how Garble literals are represented in JSON (using `serde_json`):

<pre class="abnf">
<code>literal = <span class="str">"\"True\""</span> /
          <span class="str">"\"False\""</span> /
          <span class="str">"{\"NumUnsigned\":["</span> uint <span class="str">","</span> uint-ty <span class="str">"]}"</span> /
          <span class="str">"{\"NumSigned\":["</span> int <span class="str">","</span> int-ty <span class="str">"]}"</span> /
          <span class="str">"{\"ArrayRepeat\":["</span> literal <span class="str">","</span> uint <span class="str">"]}"</span> /
          <span class="str">"{\"Array\":["</span> [literal *(<span class="str">","</span> literal)] <span class="str">"]}"</span> /
          <span class="str">"{\"Tuple\":["</span> [literal *(<span class="str">","</span> literal)] <span class="str">"]}"</span> /
          <span class="str">"{\"Enum\":[\""</span> string <span class="str">"\",\""</span> string <span class="str">"\","</span> variant <span class="str">"]}"</span> /
          <span class="str">"{\"Range\":["</span> uint <span class="str">","</span> uint <span class="str">","</span> uint-type <span class="str">"]}"</span>

uint    = 1*DIGIT

uint-ty = <span class="str">"\"Usize\""</span> /
          <span class="str">"\"U8\""</span> /
          <span class="str">"\"U16\""</span> /
          <span class="str">"\"U32\""</span> /
          <span class="str">"\"U64\""</span> /
          <span class="str">"\"Unspecified\""</span>

int     = [<span class="str">"-"</span>] uint

int-ty  = <span class="str">"\"I8\""</span> /
          <span class="str">"\"I16\""</span> /
          <span class="str">"\"I32\""</span> /
          <span class="str">"\"I64\""</span> /
          <span class="str">"\"Unspecified\""</span>

string  = 1*ALPHA

variant = <span class="str">"\"Unit\""</span> /
          <span class="str">"{\"Tuple\":["</span> [literal *(<span class="str">","</span> literal)] <span class="str">"]}"</span></code>
</pre>

Here are some example Garble literals and how they would be serialized as JSON:

| Garble Literal                   | Serialized as JSON                                       |
| -------------------------------- | -------------------------------------------------------- |
| `true`                           | `"True"`                                                 |
| `200u32`                         | `{"NumUnsigned":[200,"U32"]}`                            |
| `-200`                           | `{"NumSigned":[-200,"Unspecified"]}`                     |
| `[true; 3]`                      | `{"ArrayRepeat":["True",3]}`                             |
| `[true, false]`                  | `{"Array":["True","False"]}`                             |
| `(true, false, 10)`              | `{"Tuple":["True","False",{"NumUnsigned":[10,"U8"]}]}`   |
| `FooBar {foo: true, bar: false}` | `{"Struct":["FooBar",[["foo","True"],["bar","False"]]]}` |
| `FooBar::Foo`                    | `{"Enum":["FooBar","Foo","Unit"]}`                       |
| `FooBar::Bar(true, false)`       | `{"Enum":["FooBar","Bar",{"Tuple":["True","False"]}]}`   |
| `2u8..10u8`                      | `{"Range":[2,10,"U8"]}`                                  |


## Json-Schema
If you enable the `json_schema` feature (which also enables `serde`) the `Literal` type will implement the [`JsonSchema`](https://docs.rs/schemars/latest/schemars/trait.JsonSchema.html) trait. This enables its inclusion in APIs documented using OpenAPI documentation generators like [aide](https://docs.rs/schemars/latest/schemars/trait.JsonSchema.html) or the [dropshot](https://docs.rs/dropshot/latest/dropshot/) framework.