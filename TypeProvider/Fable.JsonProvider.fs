namespace Fable.Core

type EmitAttribute(macro: string) =
    inherit System.Attribute()

namespace Fable

module JsonProvider =

    open System
    open System.IO
    open System.Net
    open System.Text.RegularExpressions
    open System.Collections.Generic
    open FSharp.Quotations
    open FSharp.Core.CompilerServices
    open ProviderImplementation.ProvidedTypes

    open ProviderDsl
    open Fable.Core

    [<Emit("JSON.parse($0)")>]
    let jsonParse (json: string) = obj()

    [<Emit("$0[$1]")>]
    let getProp (o: obj) (k: string) = obj()

    let fetchUrlAsync (url: string) =
        async {
            let req = WebRequest.CreateHttp(url)
            req.AutomaticDecompression <- DecompressionMethods.GZip ||| DecompressionMethods.Deflate
            use! resp = req.AsyncGetResponse()
            use stream = resp.GetResponseStream()
            use reader = new IO.StreamReader(stream)
            return reader.ReadToEnd()
        }

    let firstToUpper (s: string) =
        s.[0..0].ToUpper() + s.[1..]

    let getterCode name =
        fun (args: Expr list) -> <@@ getProp %%args.Head name @@>

    let rec makeType typeName json =
        match json with
        | JsonParser.Null -> Any
        | JsonParser.Bool _ -> Bool
        | JsonParser.Number _ -> Float
        | JsonParser.String _ -> String
        | JsonParser.Array items ->
            match items with
            | [] -> Array Any
            // TODO: Check if all items have same type
            | item::_ -> makeType typeName item |> Array
        | JsonParser.Object members ->
            let members = members |> List.collect (makeMember typeName)
            makeCustomType(typeName, members) |> Custom

    and makeMember ns (name, json) =
        let t = makeType (firstToUpper name) json
        let m = Property(name, t, false, getterCode name)
        let rec makeMember' = function
            | Custom t' -> [ChildType t'; m]
            | Array t' -> makeMember' t'
            | _ -> [m]
        makeMember' t

    let parseJson logMember asm ns typeName sample =
        let makeRootType withCons basicMembers =
            makeRootType(asm, ns, typeName, [
                yield! basicMembers |> List.collect (makeMember "")
                if withCons then
                    yield Constructor(["json", String], fun args -> <@@ jsonParse %%args.Head @@>)
            ])
        match JsonParser.parse sample with
        | Some(JsonParser.Object members) ->
            members |> List.iter (fun (name,_) -> logMember name)
            makeRootType true members |> Some
        | Some(JsonParser.Array((JsonParser.Object members)::_)) ->
            let t = makeRootType false members
            let array = t.MakeArrayType() |> Custom
            [Method("ParseArray", ["json", String], array, true, fun args -> <@@ jsonParse %%args.Head @@>)]
            |> addMembers t
            Some t
        | _ -> None

    let watchers = Dictionary()

    let logLock = obj()
    let writelog logFile (text:string) =
      lock logLock <| fun () ->
        use stream = File.Open(logFile, FileMode.Append, FileAccess.Write, FileShare.ReadWrite)
        use writer = new StreamWriter(stream)
        writer.WriteLine(text.Replace("\r", "").Replace("\n","\\n"))
        writer.Flush()

    [<TypeProvider>]
    type public JsonProvider (config : TypeProviderConfig) as this =
        inherit TypeProviderForNamespaces (config)

        static let mutable nextInstance = 0
        let instance = nextInstance
        do nextInstance <- nextInstance + 1

        let logFile = Path.Combine(config.ResolutionFolder, "TypeProvider.log")
        let proc = System.Diagnostics.Process.GetCurrentProcess()

        let logtype typeName fmt =
          let logtype' text =
            sprintf "[%s][%i][%s][%s][%i]%s %s"
              (DateTime.Now.ToString("yyyy-MM-dd HH:mm:ss.fff"))
              proc.Id
              proc.ProcessName
              Environment.CommandLine
              instance
              (if String.IsNullOrEmpty typeName then "" else "[" + typeName + "]")
              text
            |> writelog logFile
          Printf.kprintf logtype' fmt

        do
          logtype "" "**** Type provider instance [%i] created" instance
          logtype "" "TypeProviderConfig.RuntimeAssembly: %s" config.RuntimeAssembly
          logtype "" "TypeProviderConfig.ResolutionFolder: %s" config.ResolutionFolder
          logtype "" "TypeProviderConfig.TemporaryFolder: %s" config.TemporaryFolder
          logtype "" "TypeProviderConfig.IsHostedExecution: %b" config.IsHostedExecution
          logtype "" "TypeProviderConfig.IsInvalidationSupported: %b" config.IsInvalidationSupported

        let asm = System.Reflection.Assembly.GetExecutingAssembly()
        let ns = "Fable.JsonProvider"

        let staticParams = [ProvidedStaticParameter("sample",typeof<string>)]
        let generator = ProvidedTypeDefinition(asm, ns, "Generator", Some typeof<obj>, isErased = true)

        do generator.DefineStaticParameters(
            parameters = staticParams,
            instantiationFunction = (fun typeName pVals ->

                    let log fmt = logtype typeName fmt
                    let logMember name = log "Member: %s" name

                    log "** Type definition requested by host"

                    let typeDef =
                        match pVals with
                        | [| :? string as arg|] ->
                            let arg = arg.Trim()
                            if Regex.IsMatch(arg, "^https?://") then
                                async {
                                    let! res = fetchUrlAsync arg
                                    return
                                        match parseJson logMember asm ns typeName res with
                                        | Some t -> t
                                        | None -> failwithf "Response from URL %s is not a valid JSON: %s" arg res
                                } |> Async.RunSynchronously
                            else
                                let content =
                                    // Check if the string is a JSON literal
                                    if arg.StartsWith("{") || arg.StartsWith("[") then arg
                                    else
                                        let filepath =
                                            if Path.IsPathRooted arg then arg
                                            else
                                                Path.GetFullPath(Path.Combine(config.ResolutionFolder, arg))

                                        if config.IsInvalidationSupported then
                                            let watcherKey = (instance, filepath)
                                            lock watchers <| fun () ->
                                                if not (watchers.ContainsKey(watcherKey)) then
                                                    // Remove prev instance watcher
                                                    let keysToRemove =
                                                      watchers
                                                      |> Seq.map (fun kvp -> kvp.Key)
                                                      |> Seq.filter (fun key -> fst key < instance)
                                                      |> Seq.toList
                                                    keysToRemove
                                                    |> List.iter (fun key ->
                                                      log "Remove file watcher: %O" key
                                                      (watchers.[key] :> IDisposable).Dispose()
                                                      watchers.Remove key |> ignore
                                                    )

                                                    let watcher =
                                                      new FileSystemWatcher(
                                                        Filter = Path.GetFileName filepath,
                                                        Path = Path.GetDirectoryName filepath,
                                                        EnableRaisingEvents = true)
                                                    let invalidate _ =
                                                      log "** Invalidate TP instance: %O" watcherKey
                                                      this.Invalidate()
                                                    watcher.Changed.Add invalidate
                                                    watcher.Deleted.Add invalidate
                                                    watcher.Renamed.Add invalidate

                                                    log "Add file watcher: %O" watcherKey
                                                    watchers.Add(watcherKey, watcher)

                                        log "Reading file"
                                        File.ReadAllText(filepath,System.Text.Encoding.UTF8)

                                log "Parsing"
                                match parseJson logMember asm ns typeName content with
                                | Some t -> t
                                | None -> failwithf "Local sample is not a valid JSON"
                        | _ -> failwith "unexpected parameter values"

                    log "Returning type definition"
                    typeDef
                )
            )

        do this.AddNamespace(ns, [generator])

    [<assembly:TypeProviderAssembly>]
    do ()
